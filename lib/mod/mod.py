from __future__ import annotations

from dataclasses import dataclass
from typing import Literal, Self, cast

from lib.toml.toml_constraint import MCVersion


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

    dependencies: set[Mod]
    """Set of dependencies. There can be 0, 1, or multiple dependencies."""

    json: dict
    """JSON used to create this object. Useful for debugging."""

    def __hash__(self) -> int:
        return hash((self.version_number, self.version_type))

    # TODO once we add Curseforge support, probably turn this into a factory
    @classmethod
    def from_modrinth_json(cls, slug: str, json: dict, dependencies: set[Mod]) -> Self:
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
            dependencies=dependencies,
            json=json,
        )

    @classmethod
    def from_batched(
        cls, raw_projects_json: list[dict], raw_versions_json: list[dict]
    ) -> list[Self]:
        # Combine mods_json and versions_json so all of a mod's info is
        # in the same place.
        # mod slug -> project/version -> mod's project/version info
        json_by_mod: dict[str, dict[Literal["project", "version"], dict | list]] = {
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

        def is_dep_in_mods(dep_id: str) -> Self | None:
            for mod in mods:
                if mod.project_id == dep_id:
                    return mod
            return None

        while True:  # TODO condition: Not all of them are done yet
            # Find a mod that has no dependencies.
            # for project, version in json_by_mod.values().values():
            # pass
            for slug, proj_ver in json_by_mod.items():
                version_json = proj_ver["version"]
                for v_json in version_json:
                    if len(v_json["dependencies"]) == 0:
                        mods.append(cls.from_modrinth_json(slug, v_json, set()))
                    else:
                        # Are ALL the dependencies already in mods?
                        # BUG This will basically just pick the first candidate.
                        # We probably need all candidates here
                        # (TODO filter by fabric manifest)
                        dep_ids = {
                            dep["project_id"]
                            for dep in v_json["dependencies"]
                            if dep["dependency_type"] == "required"
                        }

                        dependencies = cast(
                            set[Mod], {is_dep_in_mods(dep) for dep in dep_ids}
                        )

                        if all(dependencies):
                            mods.append(
                                cls.from_modrinth_json(slug, v_json, dependencies)
                            )
                            breakpoint()

        return mods


# Words to live by:
# ~ The dependent depends on the dependency. ~
