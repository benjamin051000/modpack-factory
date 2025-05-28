import argparse
import asyncio
from pathlib import Path
from pprint import pprint

import aiohttp

from lib.mod.mod import Mod
from lib.resolve.resolve_mods import solve_mods
from lib.sources import modrinth
from lib.toml import lock, mcproject


def search(args: argparse.Namespace):
    results = modrinth.search(args.query)
    print("Results:")
    for result in results["hits"]:
        print(f"{result['title']} ({result['slug']})")


def info(args: argparse.Namespace):
    result = modrinth.get_project(args.slug)
    pprint(result)


def init(args: argparse.Namespace):
    mcproject.init_mcproject_toml(args.path, args.force)


def add(args: argparse.Namespace):
    try:
        toml = mcproject.read_mcproject_toml(args.path)
    except FileNotFoundError:
        toml = mcproject.read_mcproject_toml(mcproject.init_mcproject_toml(args.path))

    # Verify the mods exist
    mods_info = modrinth.get_projects(args.mod)
    assert len(mods_info) == len(args.mod), (
        "One of the mods you entered does not exist."
    )

    for mod_info in mods_info:
        mcproject.add_mod(toml, mod_info["slug"])
        print(f"Added {mod_info['title']} ({mod_info['slug']})")

    mcproject.write_mcproject_toml(toml, args.path)

    load_all_mods(args)


def load_all_mods(args: argparse.Namespace):
    toml = mcproject.read_mcproject_toml(args.path)

    async def get_mods():
        async with aiohttp.ClientSession(modrinth.API) as session:
            tempmods = [
                Mod.from_modrinth(session, slug) for slug in toml["project"]["mods"]
            ]  # pyright: ignore
            return await asyncio.gather(*tempmods)

    mods = asyncio.run(get_mods())

    # for mod in mods:
    #     print(f"{mod.slug}: {len(mod.versions)} versions")
    #     for version in mod.versions:
    #         print("\t", version.game_versions)

    # TODO don't download it just yet. That can wait for the solver step.
    # TODO download _all_ versions for the most options...
    # TODO throw into a subdirectory I guess?
    # Later, be smart about which ones will work based on the data we already know.
    # url, filename = next(
    #     (f["url"], f["filename"]) for f in version["files"] if f["primary"]
    # )
    # modrinth.download_jar(url, filename)
    selected_stuff = solve_mods(mods)
    # print(f"Found {len(solutions)} solutions:")
    # for solution in solutions:
    #     for s in solution:
    #         # print(f"Minecraft {solution[mc_version]}")
    #         # print(f"{solution[loader]} mod loader")
    #         bool_s = solution[s]
    #         if z3.is_bool(bool_s):
    #             if bool_s:
    #                 print(s)
    #         else:
    #             print(s, solution[s])

    print(f"Selected minecraft version: {selected_stuff['mc_version']}")
    print(f"Selected mod loader: {selected_stuff['loader']}")
    print("Mods:")
    mods = selected_stuff["mods"]
    for mod in mods:
        print(f"- {mod.slug} ({mod.version_number})")

    locked_mods = lock.lock(mods)
    lock.write_lockfile(locked_mods, Path("lock.toml"))


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

    run_cmd = commands.add_parser("run", description="Load all the mods and solve.")
    run_cmd.add_argument("--path", type=Path, default=Path("mcproject.toml"))
    run_cmd.set_defaults(func=load_all_mods)

    return parser


def cli():
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
