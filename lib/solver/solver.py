from collections.abc import Callable
from textwrap import dedent

import z3

from lib.mod import Mod
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


class NoSolutionError(Exception):
    """Could not find a solution."""


def solve_mods(
    mods: list[Mod],
    mc_version_constraint: MinecraftVersionConstraint | None = None,
    dump_model: bool = False,
) -> tuple[MCVersion, str, list[Mod]]:
    """From chatgippity"""

    s = z3.Solver()

    # Map each mod release to a Boolean variable.
    # TODO consider merging this into the Mod class?
    # then you could just mod.z3_repr() or whatever
    release_vars = {
        release: z3.Bool(
            # NOTE TODO research this: do duplicate names mess up the solver?
            # Maybe they end up being the same variable?
            dedent(
                f"""\
                {release.slug}_{release.version_number}_
                {",".join(release.loaders)}_
                ({release.version_id})"""
            ).replace("\n", "")
        )
        for release in mods
    }

    # Exactly one release selected per mod.
    # Group the mods by their slug, so we can enforce only one of each slug.
    unique_slugs = {mod.slug for mod in mods}
    mods_by_unique_slug = {
        # TODO should we just make the value here release_vars[m] ? Maybe not necessary
        # if we incorporate the z3 bool into the Mod class
        slug: {mod for mod in mods if mod.slug == slug}
        for slug in unique_slugs
    }
    for unique_mods in mods_by_unique_slug.values():
        s.add(z3.AtMost(*[release_vars[m] for m in unique_mods], 1))
        s.add(z3.AtLeast(*[release_vars[m] for m in unique_mods], 1))

    # If a release is selected, the minecraft version and loader should match it.
    mc_major, mc_minor, mc_patch = z3.Ints("mc_major mc_minor mc_patch")

    if mc_version_constraint:
        if mc_version_constraint.relationship == ">=":
            s.add(mc_version_constraint.version.z3_ge(mc_major, mc_minor, mc_patch))
        elif mc_version_constraint.relationship == "":
            s.add(mc_version_constraint.version.z3_eq(mc_major, mc_minor, mc_patch))

    loader = z3.String("loader")

    for mod in mods:
        s.add(
            z3.Implies(
                release_vars[mod],
                z3.And(
                    z3.Or(
                        *[
                            v.z3_eq(mc_major, mc_minor, mc_patch)
                            for v in mod.game_versions
                        ]
                    ),
                    z3.Or(*[loader == z3.StringVal(ldr) for ldr in mod.loaders]),
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

    selected_mods: list[Mod] = []
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
