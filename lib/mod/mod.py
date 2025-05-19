from dataclasses import dataclass
from typing import Literal, Optional

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
    files: list
    jar: Optional[FabricJarConstraints]

    @classmethod
    def from_slug(cls, slug: str):  # -> list[Self]: pyright doesn't like this
        # Fetch data from source
        versions_json = modrinth.get_versions(slug)
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
    def from_slug(cls, slug: str):
        # Get info from source
        return cls(slug, ModVersion.from_slug(slug))


if __name__ == "__main__":
    mod = Mod.from_slug("sodium")
    breakpoint()
