type ('a, 'b) s =
    A of { sel_A1 : 'a ; sel_A2 : int }
  | B of { sel_B1 : 'b }
  | C of { sel_C1 : ('b, 'a) t ; sel_C2 : bool }

and ('c, 'd) t =
    X of { sel_X1 : 'c ; sel_X2 : ('c, int) s }
  | Y of { sel_Y1 : float ; sel_Y2 : 'd }


type u = int

type v = bool

let (a : (u, v) s) = assert false

let (a : (u, u) t) = assert false
