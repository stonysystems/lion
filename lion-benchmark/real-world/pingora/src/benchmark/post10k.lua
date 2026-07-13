-- W-Large: 10 KB POST body; the HTTP echo app returns the body verbatim,
-- so each request moves ~10 KB in each direction.
wrk.method = "POST"
wrk.body = string.rep("x", 10240)
wrk.headers["Content-Type"] = "application/octet-stream"
