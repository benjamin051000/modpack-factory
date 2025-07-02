from collections.abc import Callable
from textwrap import dedent

import z3

from lib.mod.mod import Mod, ModVersion
from lib.toml.toml_constraint import MCVersion, MinecraftVersionConstraint


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


def get_all_mods(root_mods: list[Mod]) -> list[Mod]:
    """Recursively get all mod releases, and their dependencies' releases."""

    visited: list[Mod] = []

    # Do a depth-first search to get all the ModVersions.
    def dfs(root_mod: Mod) -> None:
        if root_mod not in visited:
            visited.append(root_mod)

            for version in root_mod.versions:
                # Get all its dependencies, too
                for dependency in version.dependencies:
                    dfs(dependency)

    for root_mod in root_mods:
        dfs(root_mod)

    return visited


def solve_mods(
    mods: list[Mod],
    mc_version_constraint: MinecraftVersionConstraint | None = None,
    dump_model=False,
) -> tuple[MCVersion, str, list[ModVersion]]:
    """From chatgippity"""

    s = z3.Solver()

    all_mods = get_all_mods(mods)

    # Map each mod release to a Boolean variable.
    release_vars = {
        release: z3.Bool(
            # NOTE TODO research this: do duplicate names mess up the solver?
            # Maybe they end up being the same variable?
            dedent(
                f"""\
                {release.slug}_{release.version_number}_
                {",".join(release.loaders)}_
                ({release.id})"""
            ).replace("\n", "")
        )
        for mod in all_mods
        for release in mod.versions
    }

    # Exactly one release selected per mod.
    for mod in all_mods:
        s.add(z3.AtMost(*[release_vars[r] for r in mod.versions], 1))
        s.add(z3.AtLeast(*[release_vars[r] for r in mod.versions], 1))

    # If a release is selected, the minecraft version and loader should match it.
    mc_major = z3.Int("mc_major")
    mc_minor = z3.Int("mc_minor")
    mc_patch = z3.Int("mc_patch")

    if mc_version_constraint:
        if mc_version_constraint.relationship == ">=":
            s.add(mc_version_constraint.version.z3_ge(mc_major, mc_minor, mc_patch))
        elif mc_version_constraint.relationship == "":
            s.add(mc_version_constraint.version.z3_eq(mc_major, mc_minor, mc_patch))

    loader = z3.String("loader")

    for mod in all_mods:
        for release in mod.versions:
            s.add(
                z3.Implies(
                    release_vars[release],
                    z3.And(
                        z3.Or(
                            *[
                                v.z3_eq(mc_major, mc_minor, mc_patch)
                                for v in release.game_versions
                            ]
                        ),
                        z3.Or(
                            *[loader == z3.StringVal(ldr) for ldr in release.loaders]
                        ),
                    ),
                ),
            )

    if dump_model:
        for a in s.assertions():
            print(a)
    # solutions: set[z3.ModelRef] = set()
    # while s.check() == z3.sat:
    if s.check() == z3.sat:
        solution = s.model()
        # solutions.add(model)
        # BUG this isn't correct. It needs to accomodate all aspects (e.g., loader)
        # s.add(mc_version != model[mc_version])
    else:
        raise NoSolutionError

    if dump_model:
        print("sat")
        print("--dump-model passed, stopping now")
        exit()

    backwards_map = {v: k for k, v in release_vars.items()}

    selected_mods: list[ModVersion] = []
    selected_loader = solution[loader].as_string()

    selected_mc_version = MCVersion(
        solution[mc_major].as_long(),
        solution[mc_minor].as_long(),
        solution[mc_patch].as_long(),
    )

    # for solution in solutions:
    for s in solution:
        # assert isinstance(s, z3.FuncDeclRef)
        variable = s()
        value = solution[s]

        if z3.is_bool(value) and z3.is_true(value):
            selected_mods.append(backwards_map[variable])

    return selected_mc_version, selected_loader, selected_mods
