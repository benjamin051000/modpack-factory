import asyncio
import json
from dataclasses import dataclass
from io import BytesIO
from pathlib import Path
from typing import BinaryIO, Self
from zipfile import ZipFile

from lib.sources.modrinth import Modrinth


@dataclass
class Constraint:
    operand: str
    operator: str


class JarError(Exception):
    pass


@dataclass
class FabricJarConstraints:
    """Constraints collected from a Fabric mod's .jar file."""

    depends: list[Constraint]
    breaks: list[Constraint]
    recommends: list[Constraint]
    suggests: list[Constraint]
    conflicts: list[Constraint]

    @classmethod
    def _from_json(cls, data: dict) -> Self:
        # TODO how to make this more DRY?
        return cls(
            depends=[
                Constraint(dependency, operator)
                for dependency, operator in data.get("depends", {}).items()
            ],
            breaks=[
                Constraint(dependency, operator)
                for dependency, operator in data.get("breaks", {}).items()
            ],
            recommends=[
                Constraint(dependency, operator)
                for dependency, operator in data.get("recommends", {}).items()
            ],
            suggests=[
                Constraint(dependency, operator)
                for dependency, operator in data.get("suggests", {}).items()
            ],
            conflicts=[
                Constraint(dependency, operator)
                for dependency, operator in data.get("conflicts", {}).items()
            ],
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
    ) -> list[Self]:
        download_tasks = []

        for version_json in versions_json:
            files = version_json["files"]
            for file in files:
                print(f"downloading {file['filename']}...")
                download_tasks.append(cls.from_modrinth(modrinth, file["url"]))

        print(f"{len(download_tasks)=}")
        # WARNING: Takes a long time (~2GB download)
        results = await asyncio.gather(*download_tasks, return_exceptions=True)
        return [result for result in results if not isinstance(result, Exception)]
