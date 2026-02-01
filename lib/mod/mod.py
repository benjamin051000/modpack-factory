from __future__ import annotations  # TODO remove, it's deprecated

import asyncio
import sys
from dataclasses import dataclass
from typing import Literal, Self, cast

from lib.jar import FabricJarConstraints
from lib.sources.modrinth import Modrinth
from lib.toml.toml_constraint import MCVersion


# TODO move this to modrinth.py
@dataclass
class ModrinthFile:
    url: str
    filename: str
    primary: bool

    @classmethod
    def from_json(cls, json: dict) -> Self:
        return cls(
            url=json["url"],
            filename=json["filename"],
            primary=json["primary"],
        )


@dataclass
class Mod:
    """
    Representation of a Minecraft Mod.

    Primarily contains metadata about the mod, such as version constraints.

    A mod can have any number of dependencies, or none.

    The Modrinth equivalent of this data structure is a combination of a
    project ("sodium") and a version ("Sodium 0.6.13 for NeoForge 1.21.7").

    The project contains general info about the Mod.

    The version contains specific data about a particular release of the mod,
    e.g., v1.0.
    """

    ###############
    # project info
    ###############
    slug: str
    """short name for the mod"""
    project_id: str
    """UUID for the project."""

    ###############
    # version info
    ###############
    version_id: str
    """UUID for this mod version."""

    version_number: str
    """Essentially the slug of the mod version, but not generally 
    unique (e.g., "mc1.21.6-0.6.13-neoforge")."""

    game_versions: set[MCVersion]
    """Versions of Minecraft.
    Pre-releases and snapshots are not currently supported."""

    version_type: Literal["release", "alpha", "beta"]
    """Specifies the type of release: alpha, beta, or general release."""

    loaders: set[Literal["forge", "fabric", "quilt"]]
    """Loaders this mod supports. All mods support at least 1 loader."""

    # TODO consider consolidating these fields?
    files: list[ModrinthFile]
    # jar: list[FabricJarConstraints] = field(default_factory=list)
    # """List of information from the .jar downloaded file."""

    ##############################
    # Relationships to other mods
    ##############################
    # TODO slowly incorporate all of them
    # There can be 0, 1, or more in these sets.
    depends: dict[str, set[Mod]]
    """Set of candidate Mods this Mod depends on. 
    Any one Mod in each dict can satisfy this Mod's dependency constraint.
    During locking, for each dict, a candidate mod will be selected.

    Data structure: slug -> set(version, version, ...)
    """
    # breaks: set[Mod]
    # """Mods that break this one. They should not be installed together."""
    # recommends: set[Mod]
    # """Mods this one recommends. Install if user agrees."""
    # suggests: set[Mod]
    # """Mods this one suggests. Install if user agrees."""
    # conflicts: set[Mod]
    # """Mods this one conflicts with. They should not be installed together."""

    json: dict
    """JSON used to create this object. Useful for debugging."""

    def __hash__(self) -> int:
        return hash((self.version_number, self.version_type))

    # TODO once we add Curseforge support, probably turn this into a factory
    @classmethod
    def from_modrinth_json(
        cls, slug: str, json: dict, dependencies: dict[str, set[Mod]]
    ) -> Self:
        """Create a Mod from the project slug and modrinth version JSON."""
        return cls(
            slug=slug,
            project_id=json["project_id"],
            version_id=json["id"],
            version_number=json["version_number"],
            game_versions={
                MCVersion.from_str(v)
                for v in json["game_versions"]
                # Skip snapshots, pre-releases via this simple string test.
                # TODO include these
                if "-" not in v and "w" not in v
            },
            version_type=json["version_type"],
            loaders=json["loaders"],
            files=[ModrinthFile.from_json(j) for j in json["files"]],
            depends=dependencies,
            json=json,
        )

    @classmethod
    def from_batched(
        cls,
        modrinth: Modrinth,
        raw_projects_json: list[dict],
        raw_versions_json: list[dict],
        constraints: dict[str, dict[str, asyncio.Task]],
    ) -> list[Self]:
        # WARNING: Here be dragons! There is an immense amount of information in this
        # function. It's utterly ridiculous and refactors take forever because of it.
        # TODO refactor it into smaller components, if possible, so I can actually fit
        # it all in my head.

        # Combine mods_json and versions_json so all of a mod's info is
        # in the same place.
        # mod slug -> 'project'/'version' -> mod's project/version info
        slug_to_jsons: dict[str, dict[Literal["project", "version"], dict | list]] = {
            project_json["slug"]: {
                "project": project_json,
                "version": [
                    v
                    for v in raw_versions_json
                    if v["project_id"] == project_json["id"]
                ],
            }
            for project_json in raw_projects_json
        }

        mods: list[Self] = []

        for slug, proj_ver in slug_to_jsons.items():
            project = cast(dict, proj_ver["project"])
            versions = proj_ver["version"]

            for version in versions:
                constraints_for_this_version = constraints[version["id"]]

                # TODO probably doesn't need to be defaultdict because we don't
                # really update entries, they're always new, in theory.
                dependencies = {}

                # NOTE: Emma from modrinth team sent me this regarding additional files:
                # https://support.modrinth.com/en/articles/8793363-additional-files
                # So generally speaking, versions will only have one downloadable file,
                # but may also have source files, javadoc files, resource packs
                # (if it's a datapack), or "configuration templates", whatever
                # those are. TODO we definitely need to know when we are downloading
                # something that is not a normal .jar mod file, and figure out what to
                # do. If it's a source or javadoc file, it can probably be skipped.
                # At the time of writing, I don't support datapacks, but when the time
                # comes, we will need to review that, too. For now, just loop thru all.
                for files in version["files"]:
                    if files["primary"] == "false":
                        continue

                    # BUG some old versions of sodium crash here. We should catch and
                    # move on, skipping bad ones.
                    # For example, one of them has "version": "${version}". Oops.
                    try:
                        constraint_for_this_file: FabricJarConstraints = (
                            constraints_for_this_version[files["filename"]].result()
                        )
                    except ValueError as e:
                        # NOTE: If you see this error showing `${version}`, you are
                        # likely trying to parse a sources jar. These are the source
                        # files for the mod, not the actual built mod. Just skip it.
                        if "${version}" not in str(e):
                            print(f"Error getting constraints for {files['filename']}:")
                            print(e, file=sys.stderr)

                        # TODO should we skip creating the Mod itself, too?
                        # I think this makes a Mod with no dependencies...
                        continue

                    for dependency in constraint_for_this_file.depends:
                        # Check for dependencies we ignore.
                        if (
                            dependency.operand
                            in {
                                "minecraft",
                                "fabricloader",
                            }
                            or dependency.operand.startswith("fabric-rendering-")
                            or dependency.operand.startswith("fabric-block-")
                            or dependency.operand.startswith("fabric-renderer-")
                            or dependency.operand.startswith("fabric-resource-")
                        ):
                            # Skip these as they are all "built-in".
                            # TODO eventually probably add them anyway, as it'll
                            # probably simplify the solver stage.
                            # print(
                            #     f"[Mod.from_batched] ignoring dependency: {dependency}"
                            # )
                            continue

                        # Get the slug/version json info for the dependency.
                        dep_proj_ver = slug_to_jsons[dependency.operand]
                        dep_project = cast(dict, dep_proj_ver["project"])
                        dep_versions = dep_proj_ver["version"]

                        slug: str = dep_project["slug"]

                        def version_is_candidate(dep_version_json, dependency) -> bool:
                            # Compare with `file` so we use the fabric.mod.json version
                            # NOTE actually, looks like constraint_for_this_file has all the info we need (?)
                            # Get the constraint_for_this_file.version for dep_version, and then use that to see?
                            dep_version = (
                                constraints[dep_version_json["id"]][
                                    dep_version_json["files"][0]["filename"]
                                ]
                                .result()
                                .version
                            )

                            foo = dep_version in dependency.operator
                            # print(f"{'keeping' if foo else 'skipping'} {dep_version}")

                            # We may need to grab the version listed in fabric.mod.json, not the one on modrinth (they are sometimes different.)
                            # For example, one from sodium is mc1.16.3-0.1.0. The actual version is 0.1.0 I guess.
                            # Let's hope there's a clear and consistent convention... but I'm not holding my breath.
                            # Sigh... this is all such a mess.

                            return foo

                        valid_versions = [
                            dep_version
                            for dep_version in dep_versions
                            if version_is_candidate(dep_version, dependency)
                        ]
                        dependencies[slug] = valid_versions

                mods.append(
                    cls(
                        slug=slug,
                        project_id=project["id"],
                        version_id=version["id"],
                        version_number=version["version_number"],
                        game_versions=MCVersion.from_json(version["game_versions"]),
                        version_type=version["version_type"],
                        loaders=version["loaders"],
                        files=version["files"],
                        depends=dependencies,
                        json=proj_ver,
                    )
                )

        return mods


# Words to live by:
# ~ The dependent depends on the dependency. ~
