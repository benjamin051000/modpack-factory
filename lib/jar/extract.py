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
            data: dict = json.loads(archive.read("fabric.mod.json"))
        return cls._from_json(data)

    @classmethod
    async def from_modrinth(cls, modrinth: Modrinth, url: str) -> Self:
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

        return await asyncio.gather(*download_tasks)
