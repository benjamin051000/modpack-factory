from lib.sources import modrinth
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

    return parser


def cli():
    parser = create_parser()
    args = parser.parse_args()
    try:
        args.func(args)
    except AttributeError:
        parser.print_help()
        sys.exit(1)


if __name__ == "__main__":
    cli()
