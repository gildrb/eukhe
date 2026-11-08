# eukhe: the proof of LAW privacy_class_tags
#
# PROOF: case on the class: each code computes.

import Base
import ../../bend/privacy/token.bend as Tk
import ../../laws/privacy/entry.bend as PrivacyEntry

def PrivacyEntry.privacy_class_tags(c):
  match c:
    case Tk.Person{}:
      {==}
    case Tk.Email{}:
      {==}
    case Tk.Phone{}:
      {==}
    case Tk.Ip{}:
      {==}
    case Tk.Id{}:
      {==}
    case Tk.ApiKey{}:
      {==}
    case Tk.Card{}:
      {==}
    case Tk.Iban{}:
      {==}
