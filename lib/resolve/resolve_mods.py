from collections.abc import Callable

import z3

from lib.mod.mod import Mod, ModVersion


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


class NoSolutionError(Exception):
    """Could not find a solution."""


def solve_mods(mods: list[Mod]) -> tuple[str, str, list[ModVersion]]:
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
    mc_version = z3.String("mc_version")  # TODO more user-friendly name?
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
                        z3.Or(
                            *[loader == z3.StringVal(ldr) for ldr in release.loaders]
                        ),
                    ),
                ),
            )

    # solutions: set[z3.ModelRef] = set()
    # while s.check() == z3.sat:
    if s.check() == z3.sat:
        solution = s.model()
        # solutions.add(model)
        # BUG this isn't correct. It needs to accomodate all aspects (e.g., loader)
        # s.add(mc_version != model[mc_version])
    else:
        raise NoSolutionError

    backwards_map = {v: k for k, v in release_vars.items()}

    selected_mods: list[ModVersion] = []
    selected_loader = ""
    selected_mc_version = ""

    # for solution in solutions:
    for s in solution:
        # assert isinstance(s, z3.FuncDeclRef)
        variable = s()
        value = solution[s]

        if z3.is_bool(value):
            if z3.is_true(value):
                selected_mods.append(backwards_map[variable])
        elif z3.is_string(value):
            name = variable.decl().name()
            if name == "loader":
                selected_loader = value.as_string()
            elif name == "mc_version":
                selected_mc_version = value.as_string()
            else:
                raise RuntimeError("Unreachable!")

    return selected_mc_version, selected_loader, selected_mods
