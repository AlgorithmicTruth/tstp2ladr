/*  Copyright (C) 2026 Jeffrey Machado

    This file is part of tstp2ladr.

    tstp2ladr is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License, version 2.

    tstp2ladr is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with tstp2ladr; if not, write to the Free Software
    Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
*/

#ifndef FIX_POSITIONS_H
#define FIX_POSITIONS_H

#include "ladr/topform.h"
#include "ladr/just.h"
#include "ladr/xproofs.h"

/* Fix placeholder literal/term positions in a TSTP-imported proof.
   Returns number of steps that could not be fixed. */
int fix_proof_positions(Plist proof, int verbose);

/* Expand non-propositional COPY_JUST steps into binary resolution chains.
   These arise from E prover nested inferences (cn(rw(pm(...)))).
   Modifies the proof list in place (may insert intermediate steps).
   Returns number of COPY steps expanded. */
int expand_nonprop_copies(Plist *proof, int verbose);

#endif
