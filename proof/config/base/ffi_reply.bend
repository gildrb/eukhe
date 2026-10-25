# eukhe: lemmas the proofs of the config entry share (bend/ffi_config.bend),
# its replies: the entry's reply writers write what the laws' spellers
# write (each list by induction on its items).

import Base
import ../../../bend/config.bend as Cf
import ../../../bend/ffi_config.bend as FC
import ../../../bend/wire.bend as Wr
import ../../../spec/config.bend as CS

def pfr.entries_items(d: List<&2, Cf.Entry>, +rest: String) -> {FC.put_entries.items(d, rest) == CS.cf_w_entries.items(d, rest) : String}:
  match d:
    case Nil{}:
      {==}
    case e <> +t:
      match e:
        case Cf.Entry{+k, +v}:
          %pfr.entries_items(t, rest) : {Wr.put_nat(k, Wr.put_nat(v, FC.put_entries.items(t, rest))) == Wr.put_nat(k, Wr.put_nat(v, _)) : String}
          {==}

# a list of entries is written as the laws spell it
def pfr.entries(+d: List<&2, Cf.Entry>, +rest: String) -> {FC.put_entries(d, rest) == CS.cf_w_entries(d, rest) : String}:
  %pfr.entries_items(d, rest) : {Wr.put_nat(List.length(&2, Cf.Entry, d), FC.put_entries.items(d, rest)) == Wr.put_nat(List.length(&2, Cf.Entry, d), _) : String}
  {==}

def pfr.write(w: Cf.Write) -> {FC.put_write(w, "") == CS.cf_w_write(w) : String}:
  match w:
    case Cf.Refused{}:
      {==}
    case Cf.Wrote{+d}:
      %pfr.entries(d, "") : {Wr.put_nat(1n, FC.put_entries(d, "")) == Wr.put_nat(1n, _) : String}
      {==}

def pfr.lims(ls: List<&2, Cf.Lim>, +rest: String) -> {FC.put_lims.items(ls, rest) == CS.cf_w_lims(ls, rest) : String}:
  match ls:
    case Nil{}:
      {==}
    case l <> +t:
      match l:
        case Cf.Unlimited{}:
          %pfr.lims(t, rest) : {Wr.put_nat(0n, FC.put_lims.items(t, rest)) == Wr.put_nat(0n, _) : String}
          {==}
        case Cf.Cap{+n}:
          %pfr.lims(t, rest) : {Wr.put_nat(1n, Wr.put_nat(n, FC.put_lims.items(t, rest))) == Wr.put_nat(1n, Wr.put_nat(n, _)) : String}
          {==}

def pfr.founds(ms: List<&2, Maybe<&2, List<&2, Cf.Entry>>>, +rest: String) -> {FC.put_founds.items(ms, rest) == CS.cf_w_founds(ms, rest) : String}:
  match ms:
    case Nil{}:
      {==}
    case m <> +t:
      match m:
        case None{}:
          %pfr.founds(t, rest) : {Wr.put_nat(0n, FC.put_founds.items(t, rest)) == Wr.put_nat(0n, _) : String}
          {==}
        case Some{+fs}:
          %pfr.founds(t, rest) : {Wr.put_nat(1n, FC.put_entries(fs, FC.put_founds.items(t, rest))) == Wr.put_nat(1n, CS.cf_w_entries(fs, _)) : String}
          %pfr.entries(fs, FC.put_founds.items(t, rest)) : {Wr.put_nat(1n, FC.put_entries(fs, FC.put_founds.items(t, rest))) == Wr.put_nat(1n, _) : String}
          {==}

# the entry answers each request with what the laws spell
def pfr.answer(a: FC.Ask) -> {FC.answer(a) == CS.cf_w_reply(a) : String}:
  match a:
    case FC.AskRmw{r, e}:
      pfr.write(Cf.rmw(r, e))
    case FC.AskLeaves{ls}:
      {==}
    case FC.AskLimits{+s, +qs}:
      %pfr.lims(Cf.limits(s, qs), "") : {Wr.put_nat(List.length(&2, Cf.Lim, Cf.limits(s, qs)), FC.put_lims.items(Cf.limits(s, qs), "")) == Wr.put_nat(List.length(&2, Cf.Lim, Cf.limits(s, qs)), _) : String}
      {==}
    case FC.AskTrust{+t, +ks}:
      pfr.entries(Cf.project(t, Nil{}, ks), Wr.put_list(~String, ~Wr.put_str, Cf.withheld(t, ks), ""))
    case FC.AskMerge{+g, +p, +qs}:
      %pfr.founds(Cf.finds(Cf.merge(g, p), qs), "") : {Wr.put_nat(List.length(&2, Maybe<&2, List<&2, Cf.Entry>>, Cf.finds(Cf.merge(g, p), qs)), FC.put_founds.items(Cf.finds(Cf.merge(g, p), qs), "")) == Wr.put_nat(List.length(&2, Maybe<&2, List<&2, Cf.Entry>>, Cf.finds(Cf.merge(g, p), qs)), _) : String}
      {==}
