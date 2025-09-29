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

SLUGS = ["fabric-api", "sodium"]
"""List of slugs to populate the db with. 
Currently popular mods & mods with lots of releases.
NOTE: Their dependencies are also fetched.
"""


async def download_task(
    conn: sqlite3.Connection,
    cursor: sqlite3.Cursor,
    modrinth: Modrinth,
    name: str,
    url: str,
) -> None:
    # Skip if it's already in the table.
    if cursor.execute("SELECT name FROM mods WHERE name=?", (name,)).fetchone():
        return

    with BytesIO() as f:
        await modrinth.download(url, f)
        cursor.execute("INSERT INTO mods VALUES (?, ?, ?)", (name, url, f.getvalue()))
        conn.commit()


async def main():
    conn = sqlite3.connect(DB_NAME)
    cursor = conn.cursor()

    cursor.execute("""
        CREATE TABLE IF NOT EXISTS mods (
            name,
            url,
            jar
        )
    """)
    # name is the name of the file

    async with ClientSession(MODRINTH_API) as session:
        modrinth = Modrinth(session)
        mods_json, versions_json = await modrinth.get_mods_batched(SLUGS)

        print(f"num mods to download: {len(versions_json)}")

        tasks = [
            download_task(conn, cursor, modrinth, f["filename"], f["url"])
            for v in versions_json
            for f in v["files"]
        ]

        await tqdm.gather(*tasks)

    conn.close()


if __name__ == "__main__":
    asyncio.run(main())
