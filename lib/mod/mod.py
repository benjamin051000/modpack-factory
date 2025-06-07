from dataclasses import dataclass
from typing import Literal

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
    # dependencies: ?
    game_versions: list[MCVersion]
    version_type: Literal["release", "alpha", "beta"]
    loaders: list[str]
    files: list[ModrinthFile]
    id: str
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
