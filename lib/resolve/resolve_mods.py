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


# def solve_mods(mods: list[Mod]):
#     s = z3.Solver()
#
#     supported_game_versions, game_version_block = _gen_game_version_clauses(mods)
#     s.add(*supported_game_versions)
#
#     find_all_solutions(s, game_version_block)


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


def solve_mods(mods: list[Mod]):
    """From chatgippity"""

    s = z3.Solver()

    # Map each mod release to a Boolean variable.
    release_vars = {
        release: z3.Bool(f"{mod.slug}_{release.version_number}")
        for mod in mods
        for release in mod.versions
    }

    # Exactly one release selected per mod.
    for mod in mods:
        s.add(z3.AtMost(*[release_vars[r] for r in mod.versions], 1))
        s.add(z3.AtLeast(*[release_vars[r] for r in mod.versions], 1))

    # If a release is selected, the minecraft version and loader should match it.
    mc_version = z3.String("mc_version")
    loader = z3.String("loader")
    for mod in mods:
        for release in mod.versions:
            s.add(
                z3.Implies(
                    release_vars[release],
                    z3.And(
                        z3.Or(
                            *[
                                mc_version == z3.StringVal(v)
                                for v in release.game_versions
                            ]
                        ),
                        z3.Or(*[loader == z3.StringVal(l) for l in release.loaders]),
                    ),
                ),
            )

    solutions: set[z3.ModelRef] = set()
    while s.check() == z3.sat:
        model = s.model()
        solutions.add(model)
        s.add(mc_version != model[mc_version])

    print(f"Found {len(solutions)} solutions:")
    for solution in solutions:
        for s in solution:
            # print(f"Minecraft {solution[mc_version]}")
            # print(f"{solution[loader]} mod loader")
            bool_s = solution[s]
            if z3.is_bool(bool_s):
                if bool_s:
                    print(s)
            else:
                print(s, solution[s])
        # for variable in solution:
        #     if z3.is_true(variable):
        #         print(variable)
        # print('---')
