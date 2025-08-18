from __future__ import annotations

from dataclasses import dataclass
from typing import Literal, Self

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
    slug: str
    version_number: str
    game_versions: list[MCVersion]
    version_type: Literal["release", "alpha", "beta"]
    loaders: list[str]
    files: list[ModrinthFile]
    id: str
    jar: FabricJarConstraints | None
    dependencies: list[Mod]
    project_id: str | None = None

    def __hash__(self) -> int:
        return hash((self.version_number, self.version_type))

    @classmethod
    def from_json(cls, slug: str, version_json: dict) -> Self:
        return cls(
            slug=slug,
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
            dependencies=None,
            project_id=version_json["project_id"],
        )

    @classmethod
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
                slug=slug,
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


@dataclass
class Mod:
    slug: str
    versions: list[ModVersion]
    id: str | None = None

    @classmethod
    async def from_modrinth(cls, modrinth: modrinth.Modrinth, slug_or_id: str):
        # Get info from source
        # Ensure we have the real slug, not the id.
        slug = (await modrinth.get_project(slug_or_id))["slug"]
        return cls(slug, await ModVersion.from_modrinth(modrinth, slug))

    @classmethod
    def from_batched(
        cls, mods_json: list[dict], versions_json: list[dict]
    ) -> list[Self]:
        # Do it in one pass
        partial_mod_objects: list[Self] = [
            cls(mod_json["slug"], None, id=mod_json["id"]) for mod_json in mods_json
        ]

        partial_version_objects: list[ModVersion] = [
            ModVersion.from_json(slug=None, version_json=v) for v in versions_json
        ]

        # TODO Add its dependencies.
        # for partial_version in partial_version_objects:
        #     pass

        # Add versions to the mods.
        for partial_mod in partial_mod_objects:
            partial_mod.versions = [
                version
                for version in partial_version_objects
                if version.project_id == partial_mod.id
            ]

        # TODO only return root mods (not transitive deps).
        # Is this necessary/a good idea?
        return partial_mod_objects  # Which are now full
