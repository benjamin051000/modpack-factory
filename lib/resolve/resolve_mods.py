from typing import Callable
from lib.mod.mod import Mod
import z3


def find_all_solutions(s: z3.Solver, block: Callable) -> set:
    """Find all SAT solutions by blocking previous ones."""
    solutions = set()
    while s.check() == z3.sat:
        model = s.model()
        print(model)
        solutions.add(model)
        s.add(block(model))

    print(solutions)
    return solutions


def _gen_game_version_clauses(mods: list[Mod]):
    """For a list of mods, determine the list of minecraft versions they all support."""
    minecraft_version = z3.String("minecraft_version")

    supported_game_versions = [
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

    # Return the list of clauses + the block function.
    return supported_game_versions, lambda model: minecraft_version != model[
        minecraft_version
    ]


def _gen_modloader_clauses(mods: list[Mod]):
    """Generate clauses which test that the mod loader is all the same."""
    pass


def solve_mods(mods: list[Mod]):
    s = z3.Solver()

    supported_game_versions, game_version_block = _gen_game_version_clauses(mods)
    s.add(*supported_game_versions)

    find_all_solutions(s, game_version_block)


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
