# eukhe: the proof of LAW approvals_desk_detach_pieces
# PROOF: with an interactive client left the detach keeps the desk, which
# computes; with none, the rerouting of xs then ys is xs's then ys's
# (LAD.ad.rr_app, by induction on xs: each question is rerouted on its
# own), and the desk put from the two pieces is the two desks' pieces
# (LAD.ad.put2).

import Base
import ../../bend/approvals.bend as Am
import ../../laws/approvals/desk.bend as ApprovalsDesk
import ./base/desk.bend as LAD

def ApprovalsDesk.approvals_desk_detach_pieces(n, xs, ys, h, p):
  match h:
    case Am.Clients{}:
      {==}
    case Am.Nobody{}:
      %Equal.sym(List<&2, Am.Q> & List<&2, Am.Act>, Am.reroute(List.append(&2, Am.Q, xs, ys), Am.Nobody{}, p), (List.append(&2, Am.Q, LAD.ad.qs(Am.reroute(xs, Am.Nobody{}, p)), LAD.ad.qs(Am.reroute(ys, Am.Nobody{}, p))), List.append(&2, Am.Act, LAD.ad.as(Am.reroute(xs, Am.Nobody{}, p)), LAD.ad.as(Am.reroute(ys, Am.Nobody{}, p)))), LAD.ad.rr_app(xs, ys, Am.Nobody{}, p)) : {Am.detach.put(n, _) == (Am.D{n, List.append(&2, Am.Q, ApprovalsDesk.ds_qs(ApprovalsDesk.ds_desk(Am.detach.put(n, Am.reroute(xs, Am.Nobody{}, p)))), ApprovalsDesk.ds_qs(ApprovalsDesk.ds_desk(Am.detach.put(n, Am.reroute(ys, Am.Nobody{}, p)))))}, List.append(&2, Am.Act, ApprovalsDesk.ds_acts(Am.detach.put(n, Am.reroute(xs, Am.Nobody{}, p))), ApprovalsDesk.ds_acts(Am.detach.put(n, Am.reroute(ys, Am.Nobody{}, p))))) : Am.D & List<&2, Am.Act>}
      LAD.ad.put2(n, Am.reroute(xs, Am.Nobody{}, p), Am.reroute(ys, Am.Nobody{}, p))
    case Am.GatewayOnly{}:
      %Equal.sym(List<&2, Am.Q> & List<&2, Am.Act>, Am.reroute(List.append(&2, Am.Q, xs, ys), Am.GatewayOnly{}, p), (List.append(&2, Am.Q, LAD.ad.qs(Am.reroute(xs, Am.GatewayOnly{}, p)), LAD.ad.qs(Am.reroute(ys, Am.GatewayOnly{}, p))), List.append(&2, Am.Act, LAD.ad.as(Am.reroute(xs, Am.GatewayOnly{}, p)), LAD.ad.as(Am.reroute(ys, Am.GatewayOnly{}, p)))), LAD.ad.rr_app(xs, ys, Am.GatewayOnly{}, p)) : {Am.detach.put(n, _) == (Am.D{n, List.append(&2, Am.Q, ApprovalsDesk.ds_qs(ApprovalsDesk.ds_desk(Am.detach.put(n, Am.reroute(xs, Am.GatewayOnly{}, p)))), ApprovalsDesk.ds_qs(ApprovalsDesk.ds_desk(Am.detach.put(n, Am.reroute(ys, Am.GatewayOnly{}, p)))))}, List.append(&2, Am.Act, ApprovalsDesk.ds_acts(Am.detach.put(n, Am.reroute(xs, Am.GatewayOnly{}, p))), ApprovalsDesk.ds_acts(Am.detach.put(n, Am.reroute(ys, Am.GatewayOnly{}, p))))) : Am.D & List<&2, Am.Act>}
      LAD.ad.put2(n, Am.reroute(xs, Am.GatewayOnly{}, p), Am.reroute(ys, Am.GatewayOnly{}, p))
