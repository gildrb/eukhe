# eukhe: lemmas of the proof of LAW mcp_url_v4_table: the model's ranges
# against R4's blocks when the first octet is 169, one arm per second octet

import Base
import ../../../bend/mcp_url.bend as Mu
import ../../../laws/mcp_url.bend as McpUrl
import ../base/text.bend as LT

def mvt.t169(b: Nat, h: {Nat.is_le(b, 255n) == True{} : Bool}) -> {Mu.private_ab(Mu.dec(Nat.show(169n), 0), Mu.dec(Nat.show(b), 0)) == McpUrl.mu_v4_reserved(169n, b) : Bool}:
  match b:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n:
      {==}
    case 14n:
      {==}
    case 15n:
      {==}
    case 16n:
      {==}
    case 17n:
      {==}
    case 18n:
      {==}
    case 19n:
      {==}
    case 20n:
      {==}
    case 21n:
      {==}
    case 22n:
      {==}
    case 23n:
      {==}
    case 24n:
      {==}
    case 25n:
      {==}
    case 26n:
      {==}
    case 27n:
      {==}
    case 28n:
      {==}
    case 29n:
      {==}
    case 30n:
      {==}
    case 31n:
      {==}
    case 32n:
      {==}
    case 33n:
      {==}
    case 34n:
      {==}
    case 35n:
      {==}
    case 36n:
      {==}
    case 37n:
      {==}
    case 38n:
      {==}
    case 39n:
      {==}
    case 40n:
      {==}
    case 41n:
      {==}
    case 42n:
      {==}
    case 43n:
      {==}
    case 44n:
      {==}
    case 45n:
      {==}
    case 46n:
      {==}
    case 47n:
      {==}
    case 48n:
      {==}
    case 49n:
      {==}
    case 50n:
      {==}
    case 51n:
      {==}
    case 52n:
      {==}
    case 53n:
      {==}
    case 54n:
      {==}
    case 55n:
      {==}
    case 56n:
      {==}
    case 57n:
      {==}
    case 58n:
      {==}
    case 59n:
      {==}
    case 60n:
      {==}
    case 61n:
      {==}
    case 62n:
      {==}
    case 63n:
      {==}
    case 64n:
      {==}
    case 65n:
      {==}
    case 66n:
      {==}
    case 67n:
      {==}
    case 68n:
      {==}
    case 69n:
      {==}
    case 70n:
      {==}
    case 71n:
      {==}
    case 72n:
      {==}
    case 73n:
      {==}
    case 74n:
      {==}
    case 75n:
      {==}
    case 76n:
      {==}
    case 77n:
      {==}
    case 78n:
      {==}
    case 79n:
      {==}
    case 80n:
      {==}
    case 81n:
      {==}
    case 82n:
      {==}
    case 83n:
      {==}
    case 84n:
      {==}
    case 85n:
      {==}
    case 86n:
      {==}
    case 87n:
      {==}
    case 88n:
      {==}
    case 89n:
      {==}
    case 90n:
      {==}
    case 91n:
      {==}
    case 92n:
      {==}
    case 93n:
      {==}
    case 94n:
      {==}
    case 95n:
      {==}
    case 96n:
      {==}
    case 97n:
      {==}
    case 98n:
      {==}
    case 99n:
      {==}
    case 100n:
      {==}
    case 101n:
      {==}
    case 102n:
      {==}
    case 103n:
      {==}
    case 104n:
      {==}
    case 105n:
      {==}
    case 106n:
      {==}
    case 107n:
      {==}
    case 108n:
      {==}
    case 109n:
      {==}
    case 110n:
      {==}
    case 111n:
      {==}
    case 112n:
      {==}
    case 113n:
      {==}
    case 114n:
      {==}
    case 115n:
      {==}
    case 116n:
      {==}
    case 117n:
      {==}
    case 118n:
      {==}
    case 119n:
      {==}
    case 120n:
      {==}
    case 121n:
      {==}
    case 122n:
      {==}
    case 123n:
      {==}
    case 124n:
      {==}
    case 125n:
      {==}
    case 126n:
      {==}
    case 127n:
      {==}
    case 128n:
      {==}
    case 129n:
      {==}
    case 130n:
      {==}
    case 131n:
      {==}
    case 132n:
      {==}
    case 133n:
      {==}
    case 134n:
      {==}
    case 135n:
      {==}
    case 136n:
      {==}
    case 137n:
      {==}
    case 138n:
      {==}
    case 139n:
      {==}
    case 140n:
      {==}
    case 141n:
      {==}
    case 142n:
      {==}
    case 143n:
      {==}
    case 144n:
      {==}
    case 145n:
      {==}
    case 146n:
      {==}
    case 147n:
      {==}
    case 148n:
      {==}
    case 149n:
      {==}
    case 150n:
      {==}
    case 151n:
      {==}
    case 152n:
      {==}
    case 153n:
      {==}
    case 154n:
      {==}
    case 155n:
      {==}
    case 156n:
      {==}
    case 157n:
      {==}
    case 158n:
      {==}
    case 159n:
      {==}
    case 160n:
      {==}
    case 161n:
      {==}
    case 162n:
      {==}
    case 163n:
      {==}
    case 164n:
      {==}
    case 165n:
      {==}
    case 166n:
      {==}
    case 167n:
      {==}
    case 168n:
      {==}
    case 169n:
      {==}
    case 170n:
      {==}
    case 171n:
      {==}
    case 172n:
      {==}
    case 173n:
      {==}
    case 174n:
      {==}
    case 175n:
      {==}
    case 176n:
      {==}
    case 177n:
      {==}
    case 178n:
      {==}
    case 179n:
      {==}
    case 180n:
      {==}
    case 181n:
      {==}
    case 182n:
      {==}
    case 183n:
      {==}
    case 184n:
      {==}
    case 185n:
      {==}
    case 186n:
      {==}
    case 187n:
      {==}
    case 188n:
      {==}
    case 189n:
      {==}
    case 190n:
      {==}
    case 191n:
      {==}
    case 192n:
      {==}
    case 193n:
      {==}
    case 194n:
      {==}
    case 195n:
      {==}
    case 196n:
      {==}
    case 197n:
      {==}
    case 198n:
      {==}
    case 199n:
      {==}
    case 200n:
      {==}
    case 201n:
      {==}
    case 202n:
      {==}
    case 203n:
      {==}
    case 204n:
      {==}
    case 205n:
      {==}
    case 206n:
      {==}
    case 207n:
      {==}
    case 208n:
      {==}
    case 209n:
      {==}
    case 210n:
      {==}
    case 211n:
      {==}
    case 212n:
      {==}
    case 213n:
      {==}
    case 214n:
      {==}
    case 215n:
      {==}
    case 216n:
      {==}
    case 217n:
      {==}
    case 218n:
      {==}
    case 219n:
      {==}
    case 220n:
      {==}
    case 221n:
      {==}
    case 222n:
      {==}
    case 223n:
      {==}
    case 224n:
      {==}
    case 225n:
      {==}
    case 226n:
      {==}
    case 227n:
      {==}
    case 228n:
      {==}
    case 229n:
      {==}
    case 230n:
      {==}
    case 231n:
      {==}
    case 232n:
      {==}
    case 233n:
      {==}
    case 234n:
      {==}
    case 235n:
      {==}
    case 236n:
      {==}
    case 237n:
      {==}
    case 238n:
      {==}
    case 239n:
      {==}
    case 240n:
      {==}
    case 241n:
      {==}
    case 242n:
      {==}
    case 243n:
      {==}
    case 244n:
      {==}
    case 245n:
      {==}
    case 246n:
      {==}
    case 247n:
      {==}
    case 248n:
      {==}
    case 249n:
      {==}
    case 250n:
      {==}
    case 251n:
      {==}
    case 252n:
      {==}
    case 253n:
      {==}
    case 254n:
      {==}
    case 255n:
      {==}
    case 256n+p:
      LT.mt.absurdF({Mu.private_ab(Mu.dec(Nat.show(169n), 0), Mu.dec(Nat.show(256n+p), 0)) == McpUrl.mu_v4_reserved(169n, 256n+p) : Bool}, h)
