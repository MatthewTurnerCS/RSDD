/*  FuzzSMT: Fuzzing tool for Satisfiablity Modulo Theories (SMT) benchmarks.
 *  Copyright (C) 2009  Robert Daniel Brummayer
 *
 *  This file is part of FuzzSMT.
 *
 *  FuzzSMT is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  FuzzSMT is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

import java.util.*;

public enum SMTLogic {
  QF_FP; /* Added 2017? See http://smtlib.cs.uiowa.edu/logics.shtml */

  public final static HashMap<String, SMTLogic> stringToLogic;

  static {
    EnumSet<SMTLogic> set = EnumSet.range(QF_FP, QF_FP);
    stringToLogic = new HashMap<String, SMTLogic>(QF_FP.ordinal());
    for (SMTLogic logic : set) {
      stringToLogic.put(logic.toString(), logic);
    }
  }

}
