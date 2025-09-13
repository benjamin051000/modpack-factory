import json
from dataclasses import dataclass
from pathlib import Path
from typing import Self
from zipfile import ZipFile


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
    def from_jar(cls, path: Path) -> Self:
        with ZipFile(path) as archive:
            data: dict = json.loads(archive.read("fabric.mod.json"))
        return cls._from_json(data)
