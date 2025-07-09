from __future__ import annotations

from dataclasses import dataclass
from typing import Literal, Self

import aiohttp

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

    def __hash__(self) -> int:
        return hash((self.version_number, self.version_type))

    @classmethod
    async def from_modrinth(
        cls, session: aiohttp.ClientSession, slug: str
    ) -> list[Self]:
        # Fetch data from source
        versions_json = await modrinth.get_version(session, slug)

        dependency_lists: list[list[Mod]] = []
        # TODO wait on them all at once
        for version in versions_json:
            dep_list: list[Mod] = [
                await Mod.from_modrinth(session, dependency["project_id"])
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

    @classmethod
    async def from_modrinth(cls, session: aiohttp.ClientSession, slug_or_id: str):
        # Get info from source
        # Ensure we have the real slug, not the id.
        slug = (await modrinth.get_project_async(session, slug_or_id))["slug"]
        return cls(slug, await ModVersion.from_modrinth(session, slug))
