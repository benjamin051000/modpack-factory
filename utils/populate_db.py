"""
Create and populate the database.
"""

import asyncio
import sqlite3
from io import BytesIO

from aiohttp import ClientSession
from tqdm.asyncio import tqdm

from lib.sources.modrinth import MODRINTH_API, Modrinth

DB_NAME = "mods.db"

MOD_LIMIT = 10


async def download_task(
    conn: sqlite3.Connection,
    cursor: sqlite3.Cursor,
    modrinth: Modrinth,
    sha1: str,
    name: str,
    url: str,
) -> None:
    # Skip if it's already in the table.
    if cursor.execute("SELECT sha1 FROM mods WHERE sha1=?", (sha1,)).fetchone():
        return

    with BytesIO() as f:
        await modrinth.download(url, f)
        cursor.execute(
            "INSERT INTO mods VALUES (?, ?, ?)", (sha1, name, url, f.getvalue())
        )
        conn.commit()


async def main():
    conn = sqlite3.connect(DB_NAME)
    cursor = conn.cursor()

    cursor.execute("""
        CREATE TABLE IF NOT EXISTS mods (
            sha1,
            name,
            url,
            jar
        )
    """)
    # name is the name of the file

    async with ClientSession(MODRINTH_API) as session:
        modrinth = Modrinth(session)

        # Get the 100 top mods
        slugs = [
            j["slug"] for j in (await modrinth.search("", limit=MOD_LIMIT))["hits"]
        ]
        _, versions_json = await modrinth.get_mods_batched(slugs)

        print(f"num mods to download: {len(versions_json)}")

        tasks = [
            download_task(
                conn, cursor, modrinth, f["hashes"]["sha1"], f["filename"], f["url"]
            )
            for v in versions_json
            for f in v["files"]
        ]

        await tqdm.gather(*tasks)

    conn.close()


if __name__ == "__main__":
    asyncio.run(main())
