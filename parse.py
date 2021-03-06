from __future__ import print_function
from collections import defaultdict
import math
easy = ['..3.2.6..9..3.5..1..18.64....81.29..7.......8..67.82....26.95..8..2.3..9..5.1.3..',
 '2...8.3...6..7..84.3.5..2.9...1.54.8.........4.27.6...3.1..7.4.72..4..6...4.1...3',
 '......9.7...42.18....7.5.261..9.4....5.....4....5.7..992.1.8....34.59...5.7......',
 '.3..5..4...8.1.5..46.....12.7.5.2.8....6.3....4.1.9.3.25.....98..1.2.6...8..6..2.',
 '.2.81.74.7....31...9...28.5..9.4..874..2.8..316..3.2..3.27...6...56....8.76.51.9.',
 '1..92....524.1...........7..5...81.2.........4.27...9..6...........3.945....71..6',
 '.43.8.25.6.............1.949....4.7....6.8....1.2....382.5.............5.34.9.71.',
 '48...69.2..2..8..19..37..6.84..1.2....37.41....1.6..49.2..85..77..9..6..6.92...18',
 '...9....2.5.1234...3....16.9.8.......7.....9.......2.5.91....5...7439.2.4....7...',
 '..19....39..7..16..3...5..7.5......9..43.26..2......7.6..1...3..42..7..65....68..',
 '...1254....84.....42.8......3.....95.6.9.2.1.51.....6......3.49.....72....1298...',
 '.6234.75.1....56..57.....4.....948..4.......6..583.....3.....91..64....7.59.8326.',
 '3..........5..9...2..5.4....2....7..16.....587.431.6.....89.1......67.8......5437',
 '63..........5....8..5674.......2......34.1.2.......345.....7..4.8.3..9.29471...8.',
 '....2..4...8.35.......7.6.2.31.4697.2...........5.12.3.49...73........1.8....4...',
 '361.259...8.96..1.4......57..8...471...6.3...259...8..74......5.2..18.6...547.329',
 '.5.8.7.2.6...1..9.7.254...6.7..2.3.15.4...9.81.3.8..7.9...762.5.6..9...3.8.1.3.4.',
 '.8...5........3457....7.8.9.6.4..9.3..7.1.5..4.8..7.2.9.1.2....8423........1...8.',
 '..35.29......4....1.6...3.59..251..8.7.4.8.3.8..763..13.8...1.4....2......51.48..',
 '...........98.51...519.742.29.4.1.65.........14.5.8.93.267.958...51.36...........',
 '.2..3..9....9.7...9..2.8..5..48.65..6.7...2.8..31.29..8..6.5..7...3.9....3..2..5.',
 '..5.....6.7...9.2....5..1.78.415.......8.3.......928.59.7..6....3.4...1.2.....6..',
 '.4.....5...19436....9...3..6...5...21.3...5.68...2...7..5...2....24367...3.....4.',
 '..4..........3...239.7...8.4....9..12.98.13.76..2....8.1...8.539...4..........8..',
 '36..2..89...361............8.3...6.24..6.3..76.7...1.8............418...97..3..14',
 '5..4...6...9...8..64..2.........1..82.8...5.17..5.........9..84..3...6...6...3..2',
 '..72564..4.......5.1..3..6....5.8.....8.6.2.....1.7....3..7..9.2.......4..63127..',
 '..........79.5.18.8.......7..73.68..45.7.8.96..35.27..7.......5.16.3.42..........',
 '.3.....8...9...5....75.92..7..1.5..8.2..9..3.9..4.2..1..42.71....2...8...7.....9.',
 '2..17.6.3.5....1.......6.79....4.7.....8.1.....9.5....31.4.......5....6.9.6.37..2',
 '.......8.8..7.1.4..4..2..3.374...9......3......5...321.1..6..5..5.8.2..6.8.......',
 '.......85...21...996..8.1..5..8...16.........89...6..7..9.7..523...54...48.......',
 '6.8.7.5.2.5.6.8.7...2...3..5...9...6.4.3.2.5.8...5...3..5...2...1.7.4.9.4.9.6.7.1',
 '.5..1..4.1.7...6.2...9.5...2.8.3.5.1.4..7..2.9.1.8.4.6...4.1...3.4...7.9.2..6..1.',
 '.53...79...97534..1.......2.9..8..1....9.7....8..3..7.5.......3..76412...61...94.',
 '..6.8.3...49.7.25....4.5...6..317..4..7...8..1..826..9...7.2....75.4.19...3.9.6..',
 '..5.8.7..7..2.4..532.....84.6.1.5.4...8...5...7.8.3.1.45.....916..5.8..7..3.1.6..',
 '...9..8..128..64...7.8...6.8..43...75.......96...79..8.9...4.1...36..284..1..7...',
 '....8....27.....54.95...81...98.64...2.4.3.6...69.51...17...62.46.....38....9....',
 '...6.2...4...5...1.85.1.62..382.671...........194.735..26.4.53.9...2...7...8.9...',
 '...9....2.5.1234...3....16.9.8.......7.....9.......2.5.91....5...7439.2.4....7...',
 '38..........4..785..9.2.3...6..9....8..3.2..9....4..7...1.7.5..495..6..........92',
 '...158.....2.6.8...3.....4..27.3.51...........46.8.79..5.....8...4.7.1.....325...',
 '.1.5..2..9....1.....2..8.3.5...3...7..8...5..6...8...4.4.1..7.....7....6..3..4.5.',
 '.8.....4....469...4.......7..59.46...7.6.8.3...85.21..9.......5...781....6.....1.',
 '9.42....7.1..........7.65.....8...9..2.9.4.6..4...2.....16.7..........3.3....57.2',
 '...7..8....6....31.4...2....24.7.....1..3..8.....6.29....8...7.86....5....2..6...',
 '..1..7.9.59..8...1.3.....8......58...5..6..2...41......8.....3.1...2..79.2.7..4..',
 '.....3.17.15..9..8.6.......1....7.....9...2.....5....4.......2.5..6..34.34.2.....',
 '3..2........1.7...7.6.3.5...7...9.8.9...2...4.1.8...5...9.4.3.1...7.2........8..6']

hard = ['4.....8.5.3..........7......2.....6.....8.4......1.......6.3.7.5..2.....1.4......',
 '52...6.........7.13...........4..8..6......5...........418.........3..2...87.....',
 '6.....8.3.4.7.................5.4.7.3..2.....1.6.......2.....5.....8.6......1....',
 '48.3............71.2.......7.5....6....2..8.............1.76...3.....4......5....',
 '....14....3....2...7..........9...3.6.1.............8.2.....1.4....5.6.....7.8...',
 '......52..8.4......3...9...5.1...6..2..7........3.....6...1..........7.4.......3.',
 '6.2.5.........3.4..........43...8....1....2........7..5..27...........81...6.....',
 '.524.........7.1..............8.2...3.....6...9.5.....1.6.3...........897........',
 '6.2.5.........4.3..........43...8....1....2........7..5..27...........81...6.....',
 '.923.........8.1...........1.7.4...........658.........6.5.2...4.....7.....9.....',
 '6..3.2....5.....1..........7.26............543.........8.15........4.2........7..',
 '.6.5.1.9.1...9..539....7....4.8...7.......5.8.817.5.3.....5.2............76..8...',
 '..5...987.4..5...1..7......2...48....9.1.....6..2.....3..6..2.......9.7.......5..',
 '3.6.7...........518.........1.4.5...7.....6.....2......2.....4.....8.3.....5.....',
 '1.....3.8.7.4..............2.3.1...........958.........5.6...7.....8.2...4.......',
 '6..3.2....4.....1..........7.26............543.........8.15........4.2........7..',
 '....3..9....2....1.5.9..............1.2.8.4.6.8.5...2..75......4.1..6..3.....4.6.',
 '45.....3....8.1....9...........5..9.2..7.....8.........1..4..........7.2...6..8..',
 '.237....68...6.59.9.....7......4.97.3.7.96..2.........5..47.........2....8.......',
 '..84...3....3.....9....157479...8........7..514.....2...9.6...2.5....4......9..56',
 '.98.1....2......6.............3.2.5..84.........6.........4.8.93..5...........1..',
 '..247..58..............1.4.....2...9528.9.4....9...1.........3.3....75..685..2...',
 '4.....8.5.3..........7......2.....6.....5.4......1.......6.3.7.5..2.....1.9......',
 '.2.3......63.....58.......15....9.3....7........1....8.879..26......6.7...6..7..4',
 '1.....7.9.4...72..8.........7..1..6.3.......5.6..4..2.........8..53...7.7.2....46',
 '4.....3.....8.2......7........1...8734.......6........5...6........1.4...82......',
 '.......71.2.8........4.3...7...6..5....2..3..9........6...7.....8....4......5....',
 '6..3.2....4.....8..........7.26............543.........8.15........8.2........7..',
 '.47.8...1............6..7..6....357......5....1..6....28..4.....9.1...4.....2.69.',
 '......8.17..2........5.6......7...5..1....3...8.......5......2..4..8....6...3....',
 '38.6.......9.......2..3.51......5....3..1..6....4......17.5..8.......9.......7.32',
 '...5...........5.697.....2...48.2...25.1...3..8..3.........4.7..13.5..9..2...31..',
 '.2.......3.5.62..9.68...3...5..........64.8.2..47..9....3.....1.....6...17.43....',
 '.8..4....3......1........2...5...4.69..1..8..2...........3.9....6....5.....2.....',
 '..8.9.1...6.5...2......6....3.1.7.5.........9..4...3...5....2...7...3.8.2..7....4',
 '4.....5.8.3..........7......2.....6.....5.8......1.......6.3.7.5..2.....1.8......',
 '1.....3.8.6.4..............2.3.1...........958.........5.6...7.....8.2...4.......',
 '1....6.8..64..........4...7....9.6...7.4..5..5...7.1...5....32.3....8...4........',
 '249.6...3.3....2..8.......5.....6......2......1..4.82..9.5..7....4.....1.7...3...',
 '...8....9.873...4.6..7.......85..97...........43..75.......3....3...145.4....2..1',
 '...5.1....9....8...6.......4.1..........7..9........3.8.....1.5...2..4.....36....',
 '......8.16..2........7.5......6...2..1....3...8.......2......7..3..8....5...4....',
 '.476...5.8.3.....2.....9......8.5..6...1.....6.24......78...51...6....4..9...4..7',
 '.....7.95.....1...86..2.....2..73..85......6...3..49..3.5...41724................',
 '.4.5.....8...9..3..76.2.....146..........9..7.....36....1..4.5..6......3..71..2..',
 '.834.........7..5...........4.1.8..........27...3.....2.6.5....5.....8........1..',
 '..9.....3.....9...7.....5.6..65..4.....3......28......3..75.6..6...........12.3.8',
 '.26.39......6....19.....7.......4..9.5....2....85.....3..2..9..4....762.........4',
 '2.3.8....8..7...........1...6.5.7...4......3....1............82.5....6...1.......',
 '6..3.2....1.....5..........7.26............843.........8.15........8.2........7..',
 '1.....9...64..1.7..7..4.......3.....3.89..5....7....2.....6.7.9.....4.1....129.3.',
 '.........9......84.623...5....6...453...1...6...9...7....1.....4.5..2....3.8....9',
 '.2....5938..5..46.94..6...8..2.3.....6..8.73.7..2.........4.38..7....6..........5',
 '9.4..5...25.6..1..31......8.7...9...4..26......147....7.......2...3..8.6.4.....9.',
 '...52.....9...3..4......7...1.....4..8..453..6...1...87.2........8....32.4..8..1.',
 '53..2.9...24.3..5...9..........1.827...7.........981.............64....91.2.5.43.',
 '1....786...7..8.1.8..2....9........24...1......9..5...6.8..........5.9.......93.4',
 '....5...11......7..6.....8......4.....9.1.3.....596.2..8..62..7..7......3.5.7.2..',
 '.47.2....8....1....3....9.2.....5...6..81..5.....4.....7....3.4...9...1.4..27.8..',
 '......94.....9...53....5.7..8.4..1..463...........7.8.8..7.....7......28.5.26....',
 '.2......6....41.....78....1......7....37.....6..412....1..74..5..8.5..7......39..',
 '1.....3.8.6.4..............2.3.1...........758.........7.5...6.....8.2...4.......',
 '2....1.9..1..3.7..9..8...2.......85..6.4.........7...3.2.3...6....5.....1.9...2.5',
 '..7..8.....6.2.3...3......9.1..5..6.....1.....7.9....2........4.83..4...26....51.',
 '...36....85.......9.4..8........68.........17..9..45...1.5...6.4....9..2.....3...',
 '34.6.......7.......2..8.57......5....7..1..2....4......36.2..1.......9.......7.82',
 '......4.18..2........6.7......8...6..4....3...1.......6......2..5..1....7...3....',
 '.4..5..67...1...4....2.....1..8..3........2...6...........4..5.3.....8..2........',
 '.......4...2..4..1.7..5..9...3..7....4..6....6..1..8...2....1..85.9...6.....8...3',
 '8..7....4.5....6............3.97...8....43..5....2.9....6......2...6...7.71..83.2',
 '.8...4.5....7..3............1..85...6.....2......4....3.26............417........',
 '....7..8...6...5...2...3.61.1...7..2..8..534.2..9.......2......58...6.3.4...1....',
 '......8.16..2........7.5......6...2..1....3...8.......2......7..4..8....5...3....',
 '.2..........6....3.74.8.........3..2.8..4..1.6..5.........1.78.5....9..........4.',
 '.52..68.......7.2.......6....48..9..2..41......1.....8..61..38.....9...63..6..1.9',
 '....1.78.5....9..........4..2..........6....3.74.8.........3..2.8..4..1.6..5.....',
 '1.......3.6.3..7...7...5..121.7...9...7........8.1..2....8.64....9.2..6....4.....',
 '4...7.1....19.46.5.....1......7....2..2.3....847..6....14...8.6.2....3..6...9....',
 '......8.17..2........5.6......7...5..1....3...8.......5......2..3..8....6...4....',
 '963......1....8......2.5....4.8......1....7......3..257......3...9.2.4.7......9..',
 '15.3......7..4.2....4.72.....8.........9..1.8.1..8.79......38...........6....7423',
 '..........5724...98....947...9..3...5..9..12...3.1.9...6....25....56.....7......6',
 '....75....1..2.....4...3...5.....3.2...8...1.......6.....1..48.2........7........',
 '6.....7.3.4.8.................5.4.8.7..2.....1.3.......2.....5.....7.9......1....',
 '....6...4..6.3....1..4..5.77.....8.5...8.....6.8....9...2.9....4....32....97..1..',
 '.32.....58..3.....9.428...1...4...39...6...5.....1.....2...67.8.....4....95....6.',
 '...5.3.......6.7..5.8....1636..2.......4.1.......3...567....2.8..4.7.......2..5..',
 '.5.3.7.4.1.........3.......5.8.3.61....8..5.9.6..1........4...6...6927....2...9..',
 '..5..8..18......9.......78....4.....64....9......53..2.6.........138..5....9.714.',
 '..........72.6.1....51...82.8...13..4.........37.9..1.....238..5.4..9.........79.',
 '...658.....4......12............96.7...3..5....2.8...3..19..8..3.6.....4....473..',
 '.2.3.......6..8.9.83.5........2...8.7.9..5........6..4.......1...1...4.22..7..8.9',
 '.5..9....1.....6.....3.8.....8.4...9514.......3....2..........4.8...6..77..15..6.',
 '.....2.......7...17..3...9.8..7......2.89.6...13..6....9..5.824.....891..........',
 '3...8.......7....51..............36...2..4....7...........6.13..452...........8..']

hard16 = [".D4F.....856.03..5...D9..4.A62..A..1...0..2.54F...8.B...D.E.9.....9C.....D.4.E......7CB...F.......0D...A3B..F87.....2E...7...C.0.....4..C......B....F.E..0......D.7.91..E5......6.52A8..F.B.0..946..1..D.E8.3.....183B..5..........3..C.0....F.6B......2..9C8.A1", "3.8E....1..C.B.A.75.A..1.D.8..9....AE5B..0...6.26.9...34..F.....01..5.6..3..E.....2..1D0......4..4B.F..7.....9..85.C3...E2.9.....F..2...0.D1.37.....8.....7.D..B..4.............A..3.0..6.....84..ED6C9.B..08....9....8....2C43.........8..6A..D50..7....C..2.F.", "1D.B.....7.....6.35A.C.F..E....0...02.4..5..C18A4....BD..2......28..B....F..4...5.......6....8..D1A..2C.0.7.........A...48...E0C7.36.9..8..2A..........D.A...3.........65.C..0BD.2E.4.80......7F6.79.0....5F...1.5...D1.2.0C.B...C.....9.13....8...23A......5..."]

hard25 = ["M.......W.U....YEJP..I.Q....HK.M.Y.X.GC....QA.E....JT..EL..O.VA...BMIN..RUX..WSY...B.QNK...U.LOPVM....PCO......TLH.SG..RJ..A.A..YUK....B..LNG....O.VDQ....PI.FQ..Y..U.L.VW..G..X....G....HP.O....Y.TRK.NWHK.VA...L..FIS.....B.....S.I.M.T...W.........YP.....B......FA..VP.....MS..GT..I.VY.N..SU.OAQDB...F.F..Q..R..PD..N.....TC......S.DX.O...QT..MVE..UB.P...Y..F.L.GE..X.K...I...J.S..T..J.IC.F.D...PE.HO.GMOVAE..NU.W..Y...S..M.DJL...Q....SLMNIVRW.TDUK...C..K.PJ..D..S....W...YR.UV...FU..T.........XCB.N...PPMCGNDQ..T...K.L.UX.S..........WGEIMD....NV.FY.CBL.U...SKA..RH...C.BO...I....J.B..N......XTPK..DHF..V.D....PF.IC......S...N..", "VTR.H..A...CQP.G.K.N...J.Y..N.SWH.JFKX..T......BCP.DW...XI.OATJRUH......V..I..S.MV.Q...O.LX..EY..AR.F..EUT..Y.SG.H..WOP......WIKBJQE....V.M..D..C....X..YUDX.WVB....C...MILRHQ.GQ.C...U....D..BJ.YW.....A.TRSO.......N..E..LM.DKC....LY.J..K..IO.N.S.G.T.....F...GDY...T.N.PKE...W...C..WR...GQLX.MY.F..S....U.H..F.B.WE..A...G....M..W....I...B....D..U...KN....I.CHQM....O.W...R..UP..F.YNBM........R.XAU...H.R.M.C.N.OI...U.P.....XQSTQ..A..K.RC......SYTMB....E..T...S..XH.DG.F..V.M.U...HD...T....P.....Q..C.O.....R.JOKVT.SG..U.L....B.MLAQO.YR..HP...V..N..G.FJN...E.P....W.....I..XV.....V...T.G.CB.LM.PQDA....N.....I..FH.RU...M.JK..S..", ".O.K.BM..WN...PY.H..D......X.V..O..FR...GL..KC.SH.A.....E....WC...B.U.X.L..N.C..K..X..Y.S....T.OB...DR...FL..J...X..EO.S..PUAUC..QDPK..V........F...E..PG.E...W.J.DY.N.USM..X..FL..JI..AV..WU.EKBC..HT...IAM.....HGX.L..O..VJD..S...VW.R.S..MF.N..A.IUL..O.AYI.M......VR.FJN.X....Q..Q.D.BX.T.....P....AV...VE.CXR.WD.Y...O..S.B....LL.W....U.S.K.GB......YNXTKU...H.JF.S.....RYG.P..M...MTSL........H.YW..B..P.X...N....DWO.CSJ....LF.YGW....J.YUX..M..B.T.P..Q..JG.P...QBK.A..IH...CW.......QY.SAV..J...K..F..O..C..KD..G.H.B.AJ.OI...Q....T.PF.C....R..O.............US.PV...M.ND....WL...GX.NI....SK.E.QW.......CDRH...H..D.O.TG..FCUKNJ...B."]


class Grid:
    def __init__(self, problem):

        self.n = int(math.sqrt(len(problem)))
        self.spots = [(i, j) for i in range(1,self.n+1) for j in range(1,self.n+1)]

        self.domains = {} # possible assignments for each coordinate
        self.peers = {} # related spots
        self.assignment = {}
        self.unassigned = set()

        self.rows = {}
        self.cols = {}
        self.squares = {}

        self.square_set = defaultdict(set)

        self.offset = 0 if self.n == 9 else 1
        self.offset = -9 if self.n == 25 else self.offset
        self.parse(problem)

        #print(self.domains)

    def encode(self, fname='asdf.cnf'):
        var_encodings = {}
        for i in range(self.n):
            for j in range(self.n):
                for num in range(1, self.n+1):
                    #var_num = i*100 + j*10 + (num-1) + 1
                    var_num = i*self.n**2 + j*self.n + (num-1) + 1
                    var_encodings[(i, j, num)] = var_num

        encodings = []
        # square must be assigned num
        for i in range(self.n):
            for j in range(self.n):
                num_clause = ""
                for num in range(1, self.n+1):
                    num_clause += ("%d " % var_encodings[(i, j, num)])
                num_clause += "0"
                encodings.append(num_clause)

        """
        # square must only be assigned ONE num
        for i in range(self.n):
            for j in range(self.n):
                for num in range(1, self.n):
                    for other_num in range(num+1, self.n+1):
                        num_clause = "%d %d 0" % (-var_encodings[(i, j, num)], -var_encodings[(i, j, other_num)])
                        encodings.append(num_clause)

        # row/col
        for i in range(self.n):
            for num in range(1, self.n+1):
                row_clause = ""
                for j in range(self.n):
                    row_clause += ("%d " % var_encodings[(i, j, num)])
                row_clause += "0"
                encodings.append(row_clause)

        for j in range(self.n):
            for num in range(1, self.n+1):
                col_clause = ""
                for i in range(self.n):
                    col_clause += ("%d " % var_encodings[(i, j, num)])
                col_clause += "0"
                encodings.append(col_clause)

        # square set
        for square in self.square_set:
            for num in range(1, self.n+1):
                square_clause = ""
                for pos in self.square_set[square]:
                    i = pos[0]
                    j = pos[1]
                    square_clause += ("%d " % var_encodings[(i, j, num)])
                square_clause += "0"
                encodings.append(square_clause)
        """

        for i in range(self.n):
            for j in range(self.n):
                for peer in self.peers[(i, j)]:
                    for num in range(1, self.n+1):
                        different_clause = "-%d -%d 0" % (var_encodings[(i, j, num)], var_encodings[(peer[0], peer[1], num)])
                        encodings.append(different_clause)

        for i in range(self.n):
            for j in range(self.n):
                if len(self.domains[(i,j)]) == 1:
                    num = list(self.domains[(i,j)])[0]
                    encodings.append("%d 0" % var_encodings[(i, j, num)])

        with open(fname, 'w') as fout:
            header = "p cnf %d %d" % (self.n**3, len(encodings))
            fout.write(header)
            fout.write("\n")
            for l in encodings:
                fout.write(l)
                fout.write("\n")

    def decode(self, sat_encoding, display=True):
        lines = sat_encoding.split("\n")
        var_decodings = {}
        new_domains = {}
        for l in lines[1:]:
            info_arr = l[2:].split(" ")
            for var_str in info_arr:
                var_num = int(var_str)
                if var_num == 0:
                    if display:
                        self.display_sol(new_domains)
                    return new_domains
                if var_num > 0:
                    var_num -= 1
                    """
                    i = var_num / 100
                    j = (var_num % 100) / 10
                    num = (var_num % 10) + 1
                    """
                    i = var_num / (self.n**2)
                    j = (var_num % self.n**2) / self.n
                    num = (var_num % self.n) + 1
                    #print("i:", i, "j:", j, "num:", num)
                    new_domains[(i, j)] = set([num])
        return new_domains        

    def parse(self, problem, offset=0):
        for n in range(self.n):
            self.rows[n] = set(range(self.n))
            self.cols[n] = set(range(self.n))
            self.squares[n] = set(range(self.n))

        # init square_set
        n_sqrt = int(math.sqrt(self.n))
        for i in range(0, self.n):
            for j in range(0, self.n):
                pos = (i, j)
                s = (i/n_sqrt)*n_sqrt + j/n_sqrt
                self.square_set[s].add(pos)

        # get peers for each pos
        for i in range(0, self.n):
            for j in range(0, self.n):
                pos = (i, j)
                p = self.get_peers(pos)
                self.peers[pos] = p

        # init domains
        for i in range(0, self.n):
            for j in range(0, self.n):
                pos = (i, j)
                self.domains[pos] = set(range(1, self.n+1))

        # update domains with initial values
        for i in range(0, self.n):
            for j in range(0, self.n):
                c = problem[i*self.n+j] 
                pos = (i, j)
                sqrt_n = int(math.sqrt(self.n))
                s = (i/sqrt_n)*sqrt_n + j/sqrt_n
                if c == '.':
                    self.unassigned.add(pos)
                else:
                    val = ord(c)-48
                    if ord(c) >= 65:
                        val -= 7
                    val += self.offset
                    self.domains[pos] = set([val])
                    self.assignment[pos] = val
                    for p in self.peers[pos]:
                        if val in self.domains[p]:
                            self.domains[p].remove(val)

    def run_sat_solver(asdf='asdf.cnf'):
        p = Popen(['./picosat', 'asdf.cnf'], stdin=PIPE, stdout=PIPE, stderr=PIPE)
        output, err = p.communicate(b"input data that is passed to subprocess' stdin")
        rc = p.returncode
        return output

    def get_peers(self, pos):
        p = set()
        i = pos[0]
        j = pos[1]
        sqrt_n = int(math.sqrt(self.n))
        s = (i/sqrt_n)*sqrt_n + j/sqrt_n
        for other_pos in [(i, other_j) for other_j in range(self.n) if (i, other_j) != pos]:
            p.add(other_pos)
        for other_pos in [(other_i, j) for other_i in range(self.n) if (other_i, j) != pos]:
            p.add(other_pos)
        for other_pos in [square_pos for square_pos in self.square_set[s] if square_pos != pos]:
            p.add(other_pos)

        """
        if len(p) != 20:
            print("BAD")
        """

        return p

    def display(self):
        n_sqrt = int(math.sqrt(self.n))
        for i in range(0, self.n):
            for j in range(0, self.n):
                d = list(self.domains[(i,j)])
                if len(d) == 1:
                    val = d[0] - self.offset
                    if val >= 10:
                        print(chr(val-10 + ord('A')), end='')
                    else:
                        print(val, end='')
                else: 
                    print('.', end='')
                if (j+1) % n_sqrt == 0 and j+1 != self.n:
                    print(" | ", end='')
            print()
            if (i+1) % n_sqrt == 0:
                print("---------------")

    def display_sol(self, domains):
        n_sqrt = int(math.sqrt(self.n))
        print("====SAT Solution===")
        for i in range(0, self.n):
            for j in range(0, self.n):
                d = list(domains[(i,j)])
                if len(d) == 1:
                    val = d[0] - self.offset
                    if val >= 10:
                        print(chr(val-10 + ord('A')), end='')
                    else:
                        print(val, end='')
                else: 
                    print('.', end='')
                if (j+1) % n_sqrt == 0 and j+1 != self.n:
                    print(" | ", end='')
            print()
            if (i+1) % n_sqrt == 0:
                print("---------------")

for i in range(len(easy)):
    g = Grid(hard[i])
    fname = "hard%d.cnf" % i
    g.encode(fname)
