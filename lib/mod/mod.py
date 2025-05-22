import asyncio
from dataclasses import dataclass
from typing import Literal, Self

import aiohttp

from lib.jar.extract import FabricJarConstraints
from lib.sources import modrinth


@dataclass
class ModrinthFile:
    url: str
    filename: str
    primary: bool


@dataclass
class ModVersion:
    version_number: str
    # dependencies: ?
    game_versions: list[str]
    version_type: Literal["release", "alpha", "beta"]
    loaders: list[str]
    files: list[ModrinthFile]
    jar: FabricJarConstraints | None

    def __hash__(self) -> int:
        return hash((self.version_number, self.version_type))

    @classmethod
    async def from_modrinth(
        cls, session: aiohttp.ClientSession, slug: str
    ) -> list["ModVersion"]:
        # Fetch data from source
        versions_json = await modrinth.get_versions(session, slug)
        objects = [
            ModVersion(
                version_number=v["version_number"],
                game_versions=v["game_versions"],
                version_type=v["version_type"],
                loaders=v["loaders"],
                files=[
                    ModrinthFile(
                        url=f["url"],
                        filename=f["filename"],
                        primary=f["primary"],
                    )
                    for f in v["files"]
                ],
                jar=None,  # TODO smart way to pull this all in?
            )
            for v in versions_json
        ]

        return objects


@dataclass
class Mod:
    slug: str
    title: str
    description: str
    categories: str
    # client_side: Literal["required", "optional", "supported", "unknown"]
    # server_side: Literal["required", "optional", "supported", "unknown"]
    # project_type: Literal["mod", "modpack", "resourcepack", "shader"]
    issues_url: str
    source_url: str
    wiki_url: str
    versions: list[ModVersion]
    game_versions: list[str]
    loaders: list[str]

    @classmethod
    async def from_modrinth(cls, session: aiohttp.ClientSession, slug: str) -> Self:
        loop = asyncio.get_running_loop()
        mod_info = await loop.run_in_executor(None, lambda: modrinth.get_project(slug))

        assert mod_info["slug"] == slug
        assert mod_info["project_type"] == "mod"

        return cls(
            slug=slug,
            title=mod_info["title"],
            description=mod_info["description"],
            categories=mod_info["categories"],
            issues_url=mod_info["issues_url"],
            source_url=mod_info["source_url"],
            wiki_url=mod_info["wiki_url"],
            versions=await ModVersion.from_modrinth(session, slug),
            game_versions=mod_info["game_versions"],
            loaders=mod_info["loaders"],
        )
