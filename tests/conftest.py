import pytest
import pytest_asyncio
from aiohttp import ClientSession
from aiolimiter import AsyncLimiter

from lib.sources.modrinth import MODRINTH_API, RATE_LIMIT_PER_MIN, Modrinth


@pytest_asyncio.fixture(scope="session", loop_scope="session")
async def aiohttp_session():
    async with ClientSession(MODRINTH_API) as session:
        print("session")
        yield session


@pytest.fixture(scope="session")
def modrinth_rate_limiter():
    print("limiter")
    return AsyncLimiter(RATE_LIMIT_PER_MIN)


@pytest_asyncio.fixture(scope="session", loop_scope="session")
async def modrinth(aiohttp_session, modrinth_rate_limiter) -> Modrinth:
    print("modrinth")
    return Modrinth(aiohttp_session, modrinth_rate_limiter)
