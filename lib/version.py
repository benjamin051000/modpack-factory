from operator import ge, gt, le, lt
from typing import Self

from semver import Version

MAX_VERSION_NUM = 999_999


# NOTE: This cannot be a dataclass unless you're willing to change the variable order.
class VersionInterval:
    def __init__(
        self,
        min_inclusive: bool,
        min: Version | None,
        max: Version | None,
        max_inclusive: bool,
    ) -> None:
        self.min_inclusive = min_inclusive
        self.min = min if min is not None else Version(0)
        self.max = (
            max
            if max is not None
            else Version(MAX_VERSION_NUM, MAX_VERSION_NUM, MAX_VERSION_NUM)
        )
        self.max_inclusive = max_inclusive

    @classmethod
    def from_str(cls, s: str) -> Self:
        if s == "*":  # Match all versions.
            return cls(True, None, None, True)
        elif s.startswith(">="):
            return cls(True, Version.parse(s[2:]), None, True)
        elif s.startswith("<="):
            return cls(True, None, Version.parse(s[2:]), True)
        elif s.startswith(">"):
            return cls(False, Version.parse(s[1:]), None, True)
        elif s.startswith("<"):
            return cls(True, None, Version.parse(s[1:]), False)
        else:
            raise ValueError(f"Invalid version constraint: {s}")

    def __contains__(self, version: Version) -> bool:
        """Whether the interval contains version."""
        min_op = ge if self.min_inclusive else gt  # above the min
        max_op = le if self.max_inclusive else lt  # below the max
        return min_op(version, self.min) and max_op(version, self.max)
