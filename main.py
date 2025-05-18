from lib.sources import modrinth
import argparse


def search(args: argparse.Namespace):
    results = modrinth.search(args.query)
    print("Results:")
    for result in results["hits"]:
        print(f"{result["title"]} ({result["slug"]})")


def parse_args(args: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser()

    search_group = parser.add_argument_group("search", description="Search for a mod.")
    # search_group.add_argument("--from", help="Specify a source (e.g., Modrinth, Curseforge)")
    search_group.add_argument("query", help="Query to search the source for.")
    search_group.set_defaults(func=search)
    return parser.parse_args(args)


def cli():
    args = parse_args()
    args.func(args)


if __name__ == "__main__":
    cli()
