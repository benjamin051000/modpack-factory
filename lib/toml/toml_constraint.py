import re
from dataclasses import dataclass
from enum import Enum
from typing import Self, cast

import z3
from z3 import ArithRef, BoolRef

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
    patch: int = 0

    @classmethod
    def from_str(cls, value: str) -> Self:
        """Create an MCVersion from a string, like '1.20.1'.
        For strings like '1.20', the patch is defaulted to 0.
        """
        return cls(*[int(v) for v in value.split(".")])

    def __str__(self) -> str:
        if self.patch == 0:
            # Minecraft convention is to omit the patch when it's 0.
            return f"{self.major}.{self.minor}"
        else:
            return f"{self.major}.{self.minor}.{self.patch}"

    def z3_eq(self, major: ArithRef, minor: ArithRef, patch: ArithRef) -> BoolRef:
        """Create a z3 boolean expression checking for equality with
        major.minor.patch boolean variables.
        """
        expression = z3.And(
            major == self.major,
            minor == self.minor,
            patch == self.patch,
        )
        return cast(BoolRef, expression)

    def z3_ge(self, major: ArithRef, minor: ArithRef, patch: ArithRef) -> BoolRef:
        # Unfortunately, since these are overloaded operators, there is not likely
        # a way to combine these gt/ge functions. :(
        expression = z3.Or(
            major >= self.major,
            z3.And(major == self.major, minor >= self.minor),
            z3.And(
                major == self.major,
                minor == self.minor,
                patch >= self.patch,
            ),
        )
        return cast(BoolRef, expression)


@dataclass
class MinecraftVersionConstraint:
    # relationship: Relationship | None
    relationship: str  # TODO use enum
    version: MCVersion

    PATTERN = re.compile(
        r"^(?P<rel>==|<=?|>=?)?(?P<maj>\d+)\.(?P<min>\d+)(?:\.(?P<pat>\d+))?$"
    )

    @classmethod
    def from_str(cls, value: str) -> Self:
        match = cls.PATTERN.fullmatch(value)
        if match:
            return cls(
                # TODO use its from_str
                version=MCVersion(
                    major=int(match["maj"]),
                    minor=int(match["min"]),
                    patch=int(match["pat"] or "0"),
                ),
                relationship=match["rel"] or "",
            )

        raise ValueError

    def __str__(self) -> str:
        return f"{self.relationship}{self.version}"
