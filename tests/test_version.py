import pytest

from lib.jar import FabricVersionRange
from lib.version import Version, VersionInterval


@pytest.mark.parametrize(
    "s, contains_0_9_0, contains_1_0_0, contains_2_0_0",
    [
        ("<=0.1.0", False, False, False),
        (">1.0.0", False, False, True),
        (">=1.0.0", False, True, True),
        ("<1.0.0", True, False, False),
        ("<=1.0.0", True, True, False),
        ("1.0.0", False, True, False),
        (">=0.0.0", True, True, True),
    ],
)
def test_single_version_interval(
    s: str, contains_0_9_0: bool, contains_1_0_0: bool, contains_2_0_0: bool
):
    """Test single (one-ended) VersionIntervals."""
    vis = VersionInterval.from_str(s)

    assert len(vis) == 1
    vi = vis[0]

    assert (Version.parse("0.9.0") in vi) == contains_0_9_0
    assert (Version.parse("1.0.0") in vi) == contains_1_0_0
    assert (Version.parse("2.0.0") in vi) == contains_2_0_0


def test_version_constraint_comparison():
    vi = VersionInterval.from_str(">1.0.0")
    c = FabricVersionRange("sodium", vi)
    assert Version.parse("1.1.0") in c


def test_version_carat():
    s = "^1.0.0"
    correct = {
        VersionInterval(">=", Version(1, 0, 0)),
        VersionInterval("<", Version(2, 0, 0)),
    }
    vis = set(VersionInterval.from_str(s))

    assert vis == correct


def test_version_tilde():
    s = "~1.0.0"
    correct = {
        VersionInterval(">=", Version(1, 0, 0)),
        VersionInterval("<", Version(1, 1, 0)),
    }
    vis = set(VersionInterval.from_str(s))

    assert vis == correct


@pytest.mark.parametrize(
    "s",
    [
        "1.0.x",
        "1.0.X",
        "1.0.*",
    ],
)
def test_version_x_range_patch(s: str):
    vis = set(VersionInterval.from_str(s))
    correct = {
        VersionInterval(">=", Version(1, 0, 0)),
        VersionInterval("<", Version(1, 1, 0)),
    }
    assert vis == correct


@pytest.mark.parametrize(
    "s",
    [
        "1.x",
        "1.X",
        "1.*",
    ],
)
def test_version_x_range_minor(s: str):
    vis = set(VersionInterval.from_str(s))
    correct = {
        VersionInterval(">=", Version(1, 0, 0)),
        VersionInterval("<", Version(2, 0, 0)),
    }
    assert vis == correct


@pytest.mark.parametrize(
    "s",
    [
        "1.x.x",
        "1.x.X",
        "1.x.*",
        "1.X.x",
        "1.X.X",
        "1.X.*",
        "1.*.x",
        "1.*.X",
        "1.*.*",
    ],
)
def test_version_x_range_minor_double_x(s: str):
    vis = set(VersionInterval.from_str(s))
    correct = {
        VersionInterval(">=", Version(1, 0, 0)),
        VersionInterval("<", Version(2, 0, 0)),
    }
    assert vis == correct
