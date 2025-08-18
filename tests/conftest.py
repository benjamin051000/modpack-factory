import pytest
import pytest_asyncio
from aiohttp import ClientSession
from aiolimiter import AsyncLimiter

from lib.sources.modrinth import MODRINTH_API, RATE_LIMIT_PER_MIN, Modrinth


@pytest_asyncio.fixture  # TODO persist across session
async def aiohttp_session():
    async with ClientSession(MODRINTH_API) as session:
        yield session


@pytest.fixture  # TODO BUG does not persist across session
def modrinth_rate_limiter():
    return AsyncLimiter(RATE_LIMIT_PER_MIN)


@pytest_asyncio.fixture
async def modrinth(aiohttp_session, modrinth_rate_limiter) -> Modrinth:
    return Modrinth(aiohttp_session, modrinth_rate_limiter)
