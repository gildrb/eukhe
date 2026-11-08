# eukhe: the proof of LAW privacy_classes
#
# PROOF: one case per class.

import Base
import ../../bend/privacy/token.bend as Tk
import ../../laws/privacy/token.bend as PrivacyToken

def PrivacyToken.privacy_classes(c):
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
