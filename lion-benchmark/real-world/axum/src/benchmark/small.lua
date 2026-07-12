-- W-API: random small file requests
math.randomseed(os.time())
request = function()
    local id = math.random(1, 100)
    return wrk.format("GET", "/small/f" .. id .. ".bin")
end
