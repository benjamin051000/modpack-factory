import re
from dataclasses import dataclass
from enum import Enum
from typing import Self

# This is gonna be weird
# Most mods follow a sort-of semantic versioning


class Relationship(Enum):
    lt = 1  # <
    gt = 2  # >
    eq = 3  # ==
    le = 4  # <=
    ge = 5  # >=
    # ne = 6  # !=


@dataclass(order=True)
class MCVersion:
    major: int
    minor: int
    patch: int  # NOTE: .0 is typically omitted from the str.


@dataclass
class MinecraftVersionConstraint:
    version: MCVersion
    # relationship: Relationship | None
    relationship: str | None  # TODO use enum

    PATTERN = re.compile(
        r"^(?P<rel>==|<=?|>=?)?(?P<maj>\d+)\.(?P<min>\d+)(?:\.(?P<pat>\d+))?$"
    )

    @classmethod
    def from_str(cls, value: str) -> Self:
        match = cls.PATTERN.fullmatch(value)
        if match:
            return cls(
                version=MCVersion(
                    major=int(match["maj"]),
                    minor=int(match["min"]),
                    patch=int(match["pat"] or "0"),
                ),
                relationship=match["rel"],
            )

        raise ValueError
