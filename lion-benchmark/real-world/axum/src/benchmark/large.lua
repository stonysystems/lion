-- W-Static: random large file requests
math.randomseed(os.time())
request = function()
    local id = math.random(1, 100)
    return wrk.format("GET", "/large/f" .. id .. ".bin")
end
