import asyncio
import json
from collections import defaultdict
from dataclasses import dataclass
from io import BytesIO
from pathlib import Path
from typing import BinaryIO, Self
from zipfile import ZipFile

from semver import Version

from lib.sources.modrinth import Modrinth
from lib.version import VersionInterval


@dataclass
class FabricVersionRange:
    operand: str
    """A mod slug, or "minecraft", etc."""

    operators: list[VersionInterval]

    def __contains__(self, version: Version) -> bool:
        return all(version in operator for operator in self.operators)

    def __str__(self) -> str:
        return f"{self.operand}{self.operator}"

    def __repr__(self) -> str:
        return str(self)


class JarError(Exception):
    pass


@dataclass
class FabricJarConstraints:
    """Constraints collected from a Fabric mod's metadata file, fabric.mod.json."""

    id: str
    """Appears to be the mod slug"""
    version: Version
    """Version number. 
    At least in some cases, different syntactic conventions 
    may be used compared to what's on Modrinth."""

    depends: list[FabricVersionRange]
    breaks: list[FabricVersionRange]
    recommends: list[FabricVersionRange]
    suggests: list[FabricVersionRange]
    conflicts: list[FabricVersionRange]

    json: dict
    """json used to construct this object."""

    @classmethod
    def _from_json(cls, data: dict) -> Self:
        # TODO how to make this more DRY?
        def parse_constraints(keyword: str) -> list[FabricVersionRange]:
            return [
                FabricVersionRange(dependency, VersionInterval.from_str(operator))
                for dependency, operator in data.get(keyword, {}).items()
            ]

        return cls(
            id=data["id"],
            version=Version.parse(data["version"], optional_minor_and_patch=True),
            depends=parse_constraints("depends"),
            breaks=parse_constraints("breaks"),
            recommends=parse_constraints("recommends"),
            suggests=parse_constraints("suggests"),
            conflicts=parse_constraints("conflicts"),
            json=data,
        )

    @classmethod
    def from_jar(cls, path: Path | BinaryIO) -> Self:
        with ZipFile(path) as archive:
            try:
                manifest = archive.read("fabric.mod.json")
            except KeyError as e:
                # Some really old ones like fabric-api 0.0.2
                # use "mod.json", not "fabric.mod.json".
                # TODO figure out how to handle this. My guess is just exclude
                # it since there's basically 0 chance anyone uses this old of a version
                raise JarError from e

        data: dict = json.loads(manifest)

        return cls._from_json(data)

    @classmethod
    async def from_modrinth(cls, modrinth: Modrinth, url: str) -> Self:
        # TODO cache the downloads to avoid downloading again later.
        with BytesIO() as f:
            await modrinth.download(url, f)
            return cls.from_jar(f)

    @classmethod
    async def from_modrinth_batched(
        cls, modrinth: Modrinth, versions_json: list[dict]
    ) -> dict[str, dict]:
        """Return dict mapping versions_json version -> constraints"""
        results: defaultdict[str, dict[str, asyncio.Task]] = defaultdict(dict)
        download_tasks = []

        for version_json in versions_json:
            files = version_json["files"]
            for file in files:
                print(f"downloading {file['filename']}...")
                results[version_json["id"]][file["filename"]] = (
                    # TODO AI told me to make this a Task object,
                    # which apparently will fix the problem
                    asyncio.create_task(cls.from_modrinth(modrinth, file["url"]))
                )
                download_tasks.append(results[version_json["id"]][file["filename"]])

        print(f"{len(download_tasks)=}")
        # WARNING: Takes a long time (~2GB download)
        # I guess I don't need the return value because they're already
        # referenced by the results dict?
        await asyncio.gather(*download_tasks, return_exceptions=True)

        # TODO unwrap Tasks into their results? It's pretty annoying

        # Cast back to a dict so you get KeyErrors again
        return dict(results)
        # return [result for result in results if not isinstance(result, Exception)]
