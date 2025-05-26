from lib.mod.mod import Mod, ModVersion
from lib.resolve.resolve_mods import solve_mods


def test_versions():
    """Test for version matching."""
    mods = [
        Mod(
            slug="sodium",
            versions=[
                ModVersion(
                    version_number="Sodium 0.6.13 for NeoForge 1.21.5",
                    game_versions=["1.21.5"],
                    version_type="release",
                    loaders=["forge"],
                    files=[],
                    jar=None,
                )
            ],
        ),
        Mod(
            slug="iris",
            versions=[
                ModVersion(
                    version_number="Iris v123",
                    game_versions=["1.21"],
                    version_type="release",
                    loaders=["forge"],
                    files=[],
                    jar=None,
                )
            ],
        ),
    ]

    solve_mods(mods)
