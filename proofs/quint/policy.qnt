// -*- mode: Bluespec; -*-
// The security policy as an arbitrary relation.
//
// sudoers (or any other policy plugin) is abstracted to a total function from
// requests to verdicts. The model never fixes that function: it is an oracle
// whose value at a request is chosen nondeterministically the first time the
// request is consulted and remembered afterwards. Every run therefore follows
// one fixed policy, and the set of runs covers every policy over the finite
// universe, so the invariants hold for any policy.
module policy {
  import types.* from "./types"

  // Who asks to run what, where and when. `user` is the invoker identity,
  // `host` the host name and `time` the local time the policy is evaluated on.
  type Request = {
    user: int, host: str, runasUid: int, runasGid: int, cmd: str, time: int,
  }

  // deny, or allow with the authentication the matching rule requires:
  // none (NOPASSWD), the invoker's password, the target's (targetpw) or
  // root's (rootpw).
  pure val VERDICTS = Set("deny", "nopasswd", "passwd", "targetpw", "rootpw")

  type Oracle = Request -> str

  pure def consult(o: Oracle, req: Request, fresh: str): str =
    if (o.keys().contains(req)) o.get(req) else fresh

  pure def remember(o: Oracle, req: Request, fresh: str): Oracle =
    o.put(req, consult(o, req, fresh))

  pure def permits(o: Oracle, req: Request): bool =
    o.keys().contains(req) and o.get(req) != "deny"

  pure def needsAuth(v: str): bool = v != "nopasswd" and v != "deny"

  // The account whose password the verdict demands.
  pure def authPrincipal(v: str, invoker: int, target: int): int =
    if (v == "targetpw") target else if (v == "rootpw") ROOT else invoker
}
