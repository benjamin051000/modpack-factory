from lib.sources import modrinth
from lib.toml import mcproject
from pathlib import Path
import sys
from pprint import pprint
import argparse

def search(args: argparse.Namespace):
    results = modrinth.search(args.query)
    print("Results:")
    for result in results["hits"]:
        print(f"{result['title']} ({result['slug']})")


def info(args: argparse.Namespace):
    result = modrinth.get_project(args.slug)
    pprint(result)


def toml(args: argparse.Namespace):
    mcproject.init_mcproject_toml(args.path, args.force)

def add(args: argparse.Namespace):
    try:
        toml = mcproject.read_mcproject_toml(args.path)
    except FileNotFoundError:
        toml = mcproject.read_mcproject_toml(mcproject.init_mcproject_toml(args.path))

    mcproject.add_dependency(toml, args.mod)
    mcproject.write_mcproject_toml(toml, args.path)


def create_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser()

    commands = parser.add_subparsers()

    search_cmd = commands.add_parser("search", description="Search for a mod.")
    # search_group.add_argument("--from", help="Specify a source (e.g., Modrinth, Curseforge)")
    search_cmd.add_argument("query", help="Query to search the source for.")
    search_cmd.set_defaults(func=search)

    info_cmd = commands.add_parser("info", description="Get info on a mod.")
    info_cmd.add_argument("slug", help="Slug (from search result) of the mod.")
    info_cmd.set_defaults(func=info)

    toml_cmd = commands.add_parser(
        "toml", description="Make a new toml file (testing only)."
    )
    toml_cmd.add_argument("path", type=Path, nargs="?", default=Path("mcproject.toml"))
    toml_cmd.add_argument(
        "--force", action="store_true", help="Overwrite the file if it already exists."
    )
    toml_cmd.set_defaults(func=toml)

    add_cmd = commands.add_parser(
        "add", description="Add a mod to mcproject.toml."
    )
    add_cmd.add_argument("path", type=Path, nargs="?", default=Path("mcproject.toml"))
    add_cmd.add_argument(
        "mod", help="Mod to add to mcproject.toml."
    )
    add_cmd.set_defaults(func=add)
    return parser


def cli():
    parser = create_parser()
    args = parser.parse_args()
    try:
        args.func(args)
    except AttributeError:
        print("Error", file=sys.stderr)
        parser.print_help()
        sys.exit(1)


if __name__ == "__main__":
    cli()
