-- W-Mixed: 80% small + 20% large
math.randomseed(os.time())
request = function()
    local id = math.random(1, 100)
    if math.random() < 0.8 then
        return wrk.format("GET", "/small/f" .. id .. ".bin")
    else
        return wrk.format("GET", "/large/f" .. id .. ".bin")
    end
end
