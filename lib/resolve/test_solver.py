from lib.mod.mod import Mod, ModVersion
from lib.resolve.resolve_mods import solve_mods


def test_simple_resolve():
    """Test two mods that are definitely compatible."""
    mods = [
        Mod(
            slug="foo",
            versions=[
                ModVersion(
                    version_number="foo v2",
                    game_versions=["1.21.5"],
                    version_type="release",
                    loaders=["forge"],
                    files=[],
                    jar=None,
                )
            ],
        ),
        Mod(
            slug="bar",
            versions=[
                ModVersion(
                    version_number="bar v1",
                    game_versions=["1.21.5"],
                    version_type="release",
                    loaders=["forge"],
                    files=[],
                    jar=None,
                )
            ],
        ),
    ]

    solutions = solve_mods(mods)
    assert len(solutions) == 1


def test_no_compatible_version():
    """Test that there are no compatible solutions on a version mismatch."""
    mods = [
        Mod(
            slug="foo",
            versions=[
                ModVersion(
                    version_number="foo v2",
                    game_versions=["1.21.5"],
                    version_type="release",
                    loaders=["forge"],
                    files=[],
                    jar=None,
                )
            ],
        ),
        Mod(
            slug="bar",
            versions=[
                ModVersion(
                    version_number="bar v1",
                    game_versions=["1.21.4"],
                    version_type="release",
                    loaders=["forge"],
                    files=[],
                    jar=None,
                )
            ],
        ),
    ]

    solutions = solve_mods(mods)
    assert len(solutions) == 0


def test_no_compatible_loader():
    """Test that there are no compatible solutions on a loader mismatch."""
    mods = [
        Mod(
            slug="foo",
            versions=[
                ModVersion(
                    version_number="foo v2",
                    game_versions=["1.21.5"],
                    version_type="release",
                    loaders=["forge"],
                    files=[],
                    jar=None,
                )
            ],
        ),
        Mod(
            slug="bar",
            versions=[
                ModVersion(
                    version_number="bar v1",
                    game_versions=["1.21.5"],
                    version_type="release",
                    loaders=["fabric"],
                    files=[],
                    jar=None,
                )
            ],
        ),
    ]

    solutions = solve_mods(mods)
    assert len(solutions) == 0


def test_multiple_versions():
    """Test that multiple versions yield multiple solutions."""
    mods = [
        Mod(
            slug="foo",
            versions=[
                ModVersion(
                    version_number="foo v2",
                    game_versions=["1.21.5", "1.21.4"],
                    version_type="release",
                    loaders=["forge"],
                    files=[],
                    jar=None,
                )
            ],
        ),
        Mod(
            slug="bar",
            versions=[
                ModVersion(
                    version_number="bar v1",
                    game_versions=["1.21.5", "1.21.4"],
                    version_type="release",
                    loaders=["forge"],
                    files=[],
                    jar=None,
                )
            ],
        ),
    ]

    solutions = solve_mods(mods)
    assert len(solutions) == 2

    # Change the order of one of them.
    mods[1].versions[0].game_versions = ["1.21.4", "1.21.5"]

    solutions = solve_mods(mods)
    assert len(solutions) == 2


def test_multiple_loaders():
    """Test that multiple loaders yield multiple solutions."""
    mods = [
        Mod(
            slug="foo",
            versions=[
                ModVersion(
                    version_number="foo v2",
                    game_versions=["1.21.5"],
                    version_type="release",
                    loaders=["forge", "fabric"],
                    files=[],
                    jar=None,
                )
            ],
        ),
        Mod(
            slug="bar",
            versions=[
                ModVersion(
                    version_number="bar v1",
                    game_versions=["1.21.5"],
                    version_type="release",
                    loaders=["forge", "fabric"],
                    files=[],
                    jar=None,
                )
            ],
        ),
    ]

    solutions = solve_mods(mods)
    assert len(solutions) == 2

    # Change the order of one of them.
    mods[1].versions[0].loaders = ["fabric", "forge"]

    solutions = solve_mods(mods)
    assert len(solutions) == 2
