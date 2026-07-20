-- wrk load script for the work-stealing benchmark.
--
-- Each request asks the server for `n` SHA-256 iterations, where `n` is sampled
-- per request from a LOG-NORMAL distribution with a FIXED mean (WS_MEAN) and a
-- tunable coefficient of variation (WS_CV). Sweeping WS_CV increases request-cost
-- variability — the knob that work-stealing exploits — while the mean per-request
-- cost (hence total offered CPU) stays constant.
--
--   sigma^2 = ln(1 + CV^2)
--   mu      = ln(mean) - sigma^2 / 2      (so E[n] = mean, regardless of CV)
--
-- Env: WS_MEAN (mean iters/request, default 20000), WS_CV (default 1.0),
--      WS_SEED (optional, for reproducibility).

local mean = tonumber(os.getenv("WS_MEAN")) or 20000
local cv   = tonumber(os.getenv("WS_CV"))   or 1.0
local seed = tonumber(os.getenv("WS_SEED")) or 0

local sigma = math.sqrt(math.log(1.0 + cv * cv))
local mu    = math.log(mean) - 0.5 * sigma * sigma

math.randomseed(os.time() + seed + (tonumber(tostring({}):sub(8)) or 0))

-- Standard normal via Box-Muller.
local function randn()
  local u1 = math.random()
  local u2 = math.random()
  if u1 < 1e-12 then u1 = 1e-12 end
  return math.sqrt(-2.0 * math.log(u1)) * math.cos(2 * math.pi * u2)
end

request = function()
  local n = math.floor(math.exp(mu + sigma * randn()) + 0.5)
  if n < 1 then n = 1 end
  return wrk.format("GET", "/work?n=" .. n)
end
