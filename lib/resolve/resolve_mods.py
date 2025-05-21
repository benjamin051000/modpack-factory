from lib.mod.mod import Mod
import z3


def resolve_minecraft_version(mods: list[Mod]) -> list[str]:
    """For a list of mods, determine the list of minecraft versions they all support."""
    s = z3.Solver()

    minecraft_version = z3.String("minecraft_version")

    supported_versions = [
        # This Or represents all the MC versions a mod can use.
        # TODO: Keep track of which mod versions satisfy.
        z3.Or(
            [
                minecraft_version == z3.StringVal(game_version)
                for mod_version in mod.versions
                for game_version in mod_version.game_versions
            ]
        )
        for mod in mods
    ]
    s.add(*supported_versions)
    if s.check() == z3.sat:
        print(s.model())


# def test_resolve_minecraft_version_simple():
#     sodium_versions = ["1.20.4", "1.20.1", "1.21.0"]
#     lithium_versions = ["1.20.0", "1.20.1", "1.21.0"]
#
#     x = String("x")
#     s = Solver()
#     in_list1 = Or([x == StringVal(v) for v in sodium_versions])
#     in_list2 = Or([x == StringVal(v) for v in lithium_versions])
#     s.add(in_list1, in_list2)
#     breakpoint()
