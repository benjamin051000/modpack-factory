import argparse
import asyncio
import sys
from pathlib import Path
from pprint import pprint

import aiohttp
import tomlkit

from lib.mod.mod import Mod
from lib.solver.solver import NoSolutionError, get_all_mods, solve_mods
from lib.sources import modrinth
from lib.toml import lock as lockfile
from lib.toml import mcproject
from lib.toml.toml_constraint import MinecraftVersionConstraint

# TODO don't download it just yet. That can wait for the solver step.
# TODO download _all_ versions for the most options...
# TODO throw into a subdirectory I guess?
# Later, be smart about which ones will work based on the data we already know.
# url, filename = next(
#     (f["url"], f["filename"]) for f in version["files"] if f["primary"]
# )
# modrinth.download_jar(url, filename)


def search(args: argparse.Namespace) -> None:
    async def _search():
        async with aiohttp.ClientSession(modrinth.API) as session:
            return await modrinth.search(session, args.query)

    results = asyncio.run(_search())

    print("Results:")
    for result in results["hits"]:
        print(f"{result['title']} ({result['slug']})")


def info(args: argparse.Namespace) -> None:
    async def _info():
        async with aiohttp.ClientSession(modrinth.API) as session:
            return await modrinth.get_project(session, args.slug)

    result = asyncio.run(_info())
    pprint(result)


def init(args: argparse.Namespace) -> None:
    mcproject.init_mcproject_toml(args.path, args.force)


# TODO this thing is killing our rate limit. Switch to new batched methods
async def get_mods(slugs: list[str]):
    async with aiohttp.ClientSession(modrinth.API) as session:
        tempmods = [Mod.from_modrinth(session, slug) for slug in slugs]  # pyright: ignore
        return await asyncio.gather(*tempmods)


def add(args: argparse.Namespace) -> None:
    # Verify the mods exist
    print(f"Getting info for {','.join(args.mod)}...")
    mods_info = modrinth.get_projects(args.mod)
    assert len(mods_info) == len(args.mod), (
        "One of the mods you entered does not exist."
    )

    try:
        toml = mcproject.read_mcproject_toml(args.path)
    except FileNotFoundError:
        toml = mcproject.read_mcproject_toml(mcproject.init_mcproject_toml(args.path))

    for mod_info in mods_info:
        if mcproject.add_mod(toml, mod_info["slug"]):
            print(f"Adding {mod_info['title']} ({mod_info['slug']})")
        else:
            print(f"{mod_info['title']} ({mod_info['slug']}) already added.")

    mods = asyncio.run(get_mods(toml["project"]["mods"]))

    mods_and_deps = get_all_mods(mods)

    try:
        mc_version = MinecraftVersionConstraint.from_str(
            toml["project"]["minecraft-version"]
        )
    except tomlkit.exceptions.NonExistentKey:
        mc_version = None

    print("Finding a compatible set of mods...")
    try:
        lock_mods(args.path, mods_and_deps, mc_version)
    except NoSolutionError:
        print(
            f"Error: No solution found when trying to add {','.join(args.mod)}.",
            file=sys.stderr,
        )
        return

    mcproject.write_mcproject_toml(toml, args.path)


def lock(args: argparse.Namespace) -> None:
    try:
        toml = mcproject.read_mcproject_toml(args.path)
    except FileNotFoundError:
        toml = mcproject.read_mcproject_toml(mcproject.init_mcproject_toml(args.path))

    mods = asyncio.run(get_mods(toml["project"]["mods"]))
    try:
        mc_version = MinecraftVersionConstraint.from_str(
            toml["project"]["minecraft-version"]
        )
    except tomlkit.exceptions.NonExistentKey:
        mc_version = None

    all_mods = get_all_mods(mods)
    lock_mods(args.path, all_mods, mc_version, args.dump_model)


def lock_mods(
    path: Path,
    mods: list[Mod],
    mc_version: MinecraftVersionConstraint | None,
    dump_model: bool = False,
):
    selected_mc_version, selected_loader, selected_mods = solve_mods(
        mods, mc_version, dump_model
    )

    print(f"Selected minecraft version: {selected_mc_version}")
    print(f"Selected mod loader: {selected_loader}")
    print("Mods:")
    for mod in selected_mods:
        print(f"- {mod.slug} ({mod.version_number})")

    locked_mods = lockfile.lock(selected_mc_version, selected_mods)
    lock_filename = f"{path.stem}.lock.toml"
    lockfile.write_lockfile(locked_mods, Path(lock_filename))


def create_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser()

    commands = parser.add_subparsers()

    search_cmd = commands.add_parser("search", description="Search for a mod.")
    # search_group.add_argument(
    #     "--from", help="Specify a source (e.g., Modrinth, Curseforge)"
    # )
    search_cmd.add_argument("query", help="Query to search the source for.")
    search_cmd.set_defaults(func=search)

    info_cmd = commands.add_parser("info", description="Get info on a mod.")
    info_cmd.add_argument("slug", help="Slug (from search result) of the mod.")
    info_cmd.set_defaults(func=info)

    init_cmd = commands.add_parser(
        "init", description="Make a new toml file (testing only)."
    )
    init_cmd.add_argument("--path", type=Path, default=Path("mcproject.toml"))
    init_cmd.add_argument(
        "--force", action="store_true", help="Overwrite the file if it already exists."
    )
    init_cmd.set_defaults(func=init)

    add_cmd = commands.add_parser("add", description="Add a mod to mcproject.toml.")
    add_cmd.add_argument("--path", type=Path, default=Path("mcproject.toml"))
    add_cmd.add_argument("mod", nargs="+", help="Mod to add to mcproject.toml.")
    add_cmd.set_defaults(func=add)

    run_cmd = commands.add_parser("lock", description="Load all the mods and solve.")
    run_cmd.add_argument("--path", type=Path, default=Path("mcproject.toml"))
    run_cmd.add_argument(
        "--dump-model",
        action="store_true",
        required=False,
        help="Dump solver constraints.",
    )
    run_cmd.set_defaults(func=lock)

    return parser


def cli() -> None:
    parser = create_parser()
    args = parser.parse_args()
    # try:
    args.func(args)
    # except AttributeError:
    #     print("Error", file=sys.stderr)
    #     parser.print_help()
    #     sys.exit(1)


if __name__ == "__main__":
    cli()
