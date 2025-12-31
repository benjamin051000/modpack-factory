import pytest

from lib.jar import Constraint
from lib.version import Version, VersionInterval


@pytest.mark.parametrize(
    "s, contains_0_9_0, contains_1_0_0, contains_2_0_0",
    [
        (">1.0.0", False, False, True),
        (">=1.0.0", False, True, True),
        ("<1.0.0", True, False, False),
        ("<=1.0.0", True, True, False),
    ],
)
def test_version_interval_contains(
    s: str, contains_0_9_0: bool, contains_1_0_0: bool, contains_2_0_0: bool
):
    vi = VersionInterval.from_str(s)

    assert (Version.parse("0.9.0") in vi) == contains_0_9_0
    assert (Version.parse("1.0.0") in vi) == contains_1_0_0
    assert (Version.parse("2.0.0") in vi) == contains_2_0_0


def test_version_interval_comparison():
    vi = VersionInterval.from_str(">1.0.0")
    assert Version.parse("1.1.0") in vi


def test_version_constraint_comparison():
    vi = VersionInterval.from_str(">1.0.0")
    c = Constraint("sodium", vi)
    assert Version.parse("1.1.0") in c
