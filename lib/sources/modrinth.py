import sys
from json import JSONDecodeError
from pathlib import Path

import aiohttp
import requests

API = "https://api.modrinth.com/v2/"

# TODO make this into a subclass so we can dispatch to
# the appropriate one once curseforge is added.


def search(query: str) -> dict:
    response = requests.get(f"{API}search", params={"query": query})
    return response.json()


def get_project(slug: str) -> dict:
    try:
        return requests.get(f"{API}project/{slug}").json()
    except JSONDecodeError:
        print(f"Error: Mod '{slug}' not found.", file=sys.stderr)
        sys.exit(1)


def get_projects(slugs: list[str]) -> list[dict]:
    formatted_slugs = str(slugs).replace("'", '"')  # API requires double-quotes
    # NOTE: This skips ones that don't exist.
    response = requests.get(f"{API}projects", params={"ids": formatted_slugs})
    return response.json()


async def get_versions(session: aiohttp.ClientSession, slug: str) -> list:
    async with session.get(f"project/{slug}/version") as response:
        versions_json = await response.json()

    # Filter out versions which only run on a Minecraft snapshot.
    # Remove snapshots for now.
    for version in versions_json:
        version["game_versions"] = [
            v
            for v in version["game_versions"]
            # Skip snapshots, pre-releases, RCs, beta versions.
            # Sourced from modrith web filter
            if not any(
                c in v for c in ["w", "-pre", "-rc", "b", "a", "c", "rd-", "inf-"]
            )
        ]

    # Versions which only supported snapshots now have empty game_versions fields.
    filtered_versions_json = [v for v in versions_json if len(v["game_versions"])]

    return filtered_versions_json


def download_jar(url: str, filename: Path):
    response = requests.get(url, stream=True)
    with open(filename, "wb") as f:
        for chunk in response.iter_content(chunk_size=10 * 1024):  # 10kb
            f.write(chunk)
