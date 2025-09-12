from __future__ import annotations

from dataclasses import dataclass
from typing import Literal, Self
from warnings import deprecated

from lib.jar.extract import FabricJarConstraints
from lib.sources import modrinth
from lib.toml.toml_constraint import MCVersion


@dataclass
class ModrinthFile:
    url: str
    filename: str
    primary: bool


@dataclass
class ModVersion:
    # Corresponding mod's slug.
    mod_slug: str
    version_number: str
    game_versions: list[MCVersion]
    version_type: Literal["release", "alpha", "beta"]
    loaders: list[str]
    files: list[ModrinthFile]
    id: str
    jar: FabricJarConstraints | None  # TODO list[FabricJarConstraints]?
    # dependencies: mod id -> set of all ModVersions that satisfy the jar constraint
    dependencies: dict[str, set[ModVersion] | None]
    project_id: str | None = None

    def __hash__(self) -> int:
        return hash((self.version_number, self.version_type))

    # TODO once we add Curseforge support, probably turn this into a factory
    @classmethod
    def from_json(cls, mod_slug: str, version_json: dict) -> Self:
        return cls(
            mod_slug=mod_slug,
            version_number=version_json["version_number"],
            game_versions=[
                MCVersion.from_str(s)
                for s in version_json["game_versions"]
                if "-" not in s and "w" not in s  # skip snapshots, pre-releases
            ],
            version_type=version_json["version_type"],
            loaders=version_json["loaders"],
            id=version_json["id"],
            files=[
                ModrinthFile(
                    url=f["url"],
                    filename=f["filename"],
                    primary=f["primary"],
                )
                for f in version_json["files"]
            ],
            jar=None,  # TODO smart way to pull this all in?
            dependencies={
                dependency["project_id"]: None
                for dependency in version_json["dependencies"]
            },
            project_id=version_json["project_id"],
        )

    @classmethod
    @deprecated("This will almost certainly hit a rate limit. Use batched instead")
    async def from_modrinth(cls, modrinth: modrinth.Modrinth, slug: str) -> list[Self]:
        # Fetch data from source
        versions_json = await modrinth.get_version(slug)

        dependency_lists: list[list[Mod]] = []
        # TODO wait on them all at once
        for version in versions_json:
            dep_list: list[Mod] = [
                await Mod.from_modrinth(modrinth, dependency["project_id"])
                for dependency in version["dependencies"]
                if dependency["dependency_type"] == "required"
            ]
            dependency_lists.append(dep_list)

        objects = [
            cls(
                mod_slug=slug,
                version_number=v["version_number"],
                game_versions=[MCVersion.from_str(s) for s in v["game_versions"]],
                version_type=v["version_type"],
                loaders=v["loaders"],
                id=v["id"],
                files=[
                    ModrinthFile(
                        url=f["url"],
                        filename=f["filename"],
                        primary=f["primary"],
                    )
                    for f in v["files"]
                ],
                jar=None,  # TODO smart way to pull this all in?
                dependencies=dep_list,
            )
            for v, dep_list in zip(versions_json, dependency_lists, strict=False)
        ]

        return objects


# TODO this class is useless. Combine it with ModVersion... unless Curseforge does
# things differently and it suddenly makes more sense to keep these separate.
# Right now this is modeled after the Modrinth API, though, which is suboptimal.
@dataclass
class Mod:
    # HACK: None means "not yet known". They should never actually be None post-setup
    slug: str
    versions: set[ModVersion]
    id: str | None = None  # TODO FIXME why is this = None

    @classmethod
    @deprecated("Use the batched version or be rate-limited")
    async def from_modrinth(cls, modrinth: modrinth.Modrinth, slug_or_id: str):
        # Get info from source
        # Ensure we have the real slug, not the id.
        slug = (await modrinth.get_project(slug_or_id))["slug"]
        return cls(slug, await ModVersion.from_modrinth(modrinth, slug))

    @classmethod
    def from_batched(
        cls, mods_json: list[dict], versions_json: list[dict]
    ) -> list[Self]:
        mods: list[Self] = []

        # Add versions to the mods.
        for mod_json in mods_json:
            versions: set[ModVersion] = {
                ModVersion.from_json(mod_json["slug"], version)
                for version in versions_json
                if version["project_id"] == mod_json["id"]
            }

            mod = cls(mod_json["slug"], versions, mod_json["id"])
            mods.append(mod)

        for mod in mods:
            for version in mod.versions:
                # type == ModVersion id
                dependency_mod_ids = version.dependencies.keys()

                for dependency_id in dependency_mod_ids:
                    dependent_mod = next(mod for mod in mods if mod.id == dependency_id)

                    # TODO actually get the constraint from the jar manifest file,
                    # and filter dependent_mod.versions to ones that satisfy it.
                    # Until then, just set it to all candidates as a proof-of-concept.
                    version.dependencies[dependency_id] = dependent_mod.versions

        # TODO consider post-validation that all fields are not None
        # TODO only return root mods (not transitive deps).
        # Is this necessary/a good idea?
        return mods  # Which are now full


# ~ The dependent depends on the dependency. ~
