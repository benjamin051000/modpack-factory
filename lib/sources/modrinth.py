import asyncio
import sys
from itertools import batched
from json import JSONDecodeError
from pathlib import Path

import aiohttp
import requests
from aiolimiter import AsyncLimiter

API = "https://api.modrinth.com/v2/"

# I was told by a SWE @ Modrinth that 800 is generally the
# limit Cloudflare allows. So, batch in 800s.
BATCH_LIMIT = 800

# The docs state that modrinth rate limits at 300 requests per minute.
rate_limit = AsyncLimiter(300)

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


async def get_project_async(session: aiohttp.ClientSession, slug_or_id: str) -> dict:
    async with rate_limit, session.get(f"project/{slug_or_id}") as response:
        return await response.json()


def get_projects(slugs: list[str]) -> list[dict]:
    formatted_slugs = str(slugs).replace("'", '"')  # API requires double-quotes
    # NOTE: This skips ones that don't exist.
    response = requests.get(f"{API}projects", params={"ids": formatted_slugs})
    return response.json()


async def get_projects_async(
    session: aiohttp.ClientSession, slugs: list[str]
) -> list[dict]:
    formatted_slugs = str(slugs).replace("'", '"')  # API requires double-quotes
    async with (
        rate_limit,
        session.get("projects", params={"ids": formatted_slugs}) as response,
    ):
        return await response.json()


async def get_version(session: aiohttp.ClientSession, slug: str) -> list:
    async with rate_limit, session.get(f"project/{slug}/version") as response:
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


async def get_versions(session: aiohttp.ClientSession, version_ids: list[str]) -> list:
    formatted_ids = str(version_ids).replace("'", '"')
    async with (
        rate_limit,
        session.get("versions", params={"ids": formatted_ids}) as response,
    ):
        try:
            versions: list = await response.json()
        except aiohttp.ContentTypeError:
            text_response = await response.text()
            print(text_response, file=sys.stderr)
            sys.exit(1)
    return versions


# TODO decorate get_versions and get_project_async
async def get_versions_batched(
    session: aiohttp.ClientSession, version_ids: list[str]
) -> list:
    tasks = [
        get_versions(session, list(batch))
        for batch in batched(version_ids, BATCH_LIMIT, strict=False)
    ]

    results = await asyncio.gather(*tasks)
    return [item for result in results for item in result]


def download_jar(url: str, filename: Path):
    response = requests.get(url, stream=True)
    with open(filename, "wb") as f:
        for chunk in response.iter_content(chunk_size=10 * 1024):  # 10kb
            f.write(chunk)
