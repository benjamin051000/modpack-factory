from dataclasses import dataclass
from typing import Literal, Optional

import aiohttp

from lib.sources import modrinth
from lib.jar.extract import FabricJarConstraints


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
    jar: Optional[FabricJarConstraints]

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
    versions: list[ModVersion]

    @classmethod
    async def from_modrinth(cls, session: aiohttp.ClientSession, slug: str):
        # Get info from source
        return cls(slug, await ModVersion.from_modrinth(session, slug))
