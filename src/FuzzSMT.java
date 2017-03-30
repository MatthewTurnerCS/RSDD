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

public class FuzzSMT {

	/*----------------------------------------------------------------------------*/
	/* Auxillary                                                                  */
	/*----------------------------------------------------------------------------*/

	// TODO: Define any needed enums for FP logic
	private enum FPRoundMode {
		RNE,	// Round nearest ties to even
		RNA,	// Round nearest ties to away
		RTP,	// Round toward positive
		RTN,	// Round toward negative
		RTZ		// Round toward zero
	}

	private static int selectRandValRange (Random r, int min, int max){
		int result;
		assert (r != null); assert (min >= 0); assert (max >= 0); assert (max >= min);
		result = r.nextInt(max - min + 1) + min;
		assert (result >= min); assert (result <= max);
		return result;
	}

	private static void updateNodeRefs (HashMap<SMTNode, Integer> map, 
			SMTNode node, int minRefs){
		Integer refs;

		assert (map != null); assert (node != null); assert (minRefs > 0);

		refs = map.get(node);
		if (refs != null) {
			refs = new Integer (refs.intValue() + 1);
			if (refs.intValue() >= minRefs)
				map.remove(node);
			else
				map.put (node, refs);
		}
	}

	private static void updateFuncRefs (HashMap<UFunc, Integer> map, 
			UFunc uFunc, int minRefs){
		Integer refs;

		assert (map != null); assert (uFunc != null); assert (minRefs > 0);

		refs = map.get(uFunc);
		if (refs != null) {
			refs = new Integer (refs.intValue() + 1);
			if (refs.intValue() >= minRefs)
				map.remove(uFunc);
			else
				map.put (uFunc, refs);
		}
	}

	private static void updatePredRefs (HashMap<UPred, Integer> map, 
			UPred uPred, int minRefs){
		Integer refs;

		assert (map != null); assert (uPred != null); assert (minRefs > 0);

		refs = map.get(uPred);
		if (refs != null) {
			refs = new Integer (refs.intValue() + 1);
			if (refs.intValue() >= minRefs)
				map.remove(uPred);
			else
				map.put (uPred, refs);
		}
	}

	/*----------------------------------------------------------------------------*/
	/* Input Layer                                                                */
	/*----------------------------------------------------------------------------*/

	private static int generateFPVars (Random r, List<SMTNode> nodes, int numVars, short fpMode) {
		//TODO: Build input layer for FP (vars)
		assert (nodes != null);
		assert (numVars >= 0);
		StringBuilder builder = new StringBuilder();
		String name;
		for(int i=0; i < numVars; i++){
			name = "v" + SMTNode.getNodeCtr();
			int bw = SMTFloat.randomBitWidth(r, fpMode);
			//builder.append (":extrafuns ((");
			//builder.append (name);
			//builder.append (" Float");
			//builder.append (bw);
			//builder.append ("))\n");
						
			builder.append("(declare-const ");
			builder.append(name);
			builder.append(" Float");
			builder.append(bw);
			builder.append(")\n");
			nodes.add (new SMTNode (new FloatType(bw), name));
		}
		System.out.print (builder.toString());
		return numVars;
	}

	private static int generateFPConsts(Random r, List<SMTNode> nodes, int numConsts,
			short fpMode) {
		//TODO: Build input layer for FP (consts)
		String name;	    
		StringBuilder builder;

		assert (nodes != null);
		assert (r != null);
		assert (nodes != null);
		assert (numConsts >= 0);	    
		assert(fpMode > 0 && fpMode < 16);

		builder = new StringBuilder();
		for (int i = 0; i < numConsts; i++) {
			name = "?e" + SMTNode.getNodeCtr();

			int bw = SMTFloat.randomBitWidth(r, fpMode);			
			SMTFloat floatConst = SMTFloat.GenerateFloat(bw, r);

			//builder.append ("(let (");
			//builder.append (name);
			//builder.append (" ");
			//builder.append (floatConst.toString());
			//builder.append (")\n");
			
			builder.append("(declare-const ");
			builder.append(name);
			builder.append(" Float" + bw);
			builder.append(")\n");
			builder.append("(assert (= " + name + " (fp " + floatConst.toString() + ")))\n");
			
			nodes.add (new SMTNode (new FloatType(bw), name));
		}
		System.out.print (builder.toString());

		return numConsts;
	}

	private static int generateUPredsFP(Random r, ArrayList<UPred> preds, int numPreds, int minArgs, int maxArgs,
			short fpMode) {
		// TODO: Generate FP UPreds
		int numArgs;
		Signature sig;
		ArrayList<SMTType> operandTypes;
		String name;
		StringBuilder builder;

		assert (r != null);
		assert (preds != null);
		assert (numPreds >= 0);
		assert (minArgs >= 1);
		assert (maxArgs >= minArgs);		

		builder = new StringBuilder();
		for (int i = 0; i < numPreds; i++){
			name = "p" + UPred.getPredsCtr();
			numArgs = selectRandValRange (r, minArgs, maxArgs);
			assert (numArgs >= minArgs);
			assert (numArgs <= maxArgs);
			operandTypes = new ArrayList<SMTType>(numArgs);

			for (int j = 0; j < numArgs; j++) {
				int bw = SMTFloat.randomBitWidth(r, fpMode);
				operandTypes.add (new FloatType(bw));
			}
			sig = new Signature (operandTypes, BoolType.boolType);
			builder.append("(declare-fun ");
			preds.add (new UPred (name, sig));
			//builder.append (":extrapreds ((");
			builder.append (name);
			builder.append(" (");
			for (int j = 0; j < numArgs; j++) {
				if(j!= 0) builder.append (" ");
				builder.append (operandTypes.get(j).toString());
			}
			builder.append(")");
			builder.append(" Bool");
			builder.append (")\n");
		}
		System.out.print (builder.toString());
		return numPreds;
	}

	private static int generateUFuncsFP(Random r, ArrayList<UFunc> funcs, int numFuncs, int minArgs, int maxArgs,
			short fpMode) {
		// TODO: Generate FP UFuncs
		int numArgs, bw;
		Signature sig;
		ArrayList<SMTType> operandTypes;
		SMTType resultType;
		String name;
		StringBuilder builder;

		assert (r != null);
		assert (funcs != null);
		assert (numFuncs >= 0);
		assert (minArgs >= 1);
		assert (maxArgs >= minArgs);		

		builder = new StringBuilder();
		for (int i = 0; i < numFuncs; i++) {
			name = "f" + UFunc.getFuncsCtr();
			numArgs = selectRandValRange (r, minArgs, maxArgs);
			assert (numArgs >= minArgs);
			assert (numArgs <= maxArgs);
			operandTypes = new ArrayList<SMTType>(numArgs);
			for (int j = 0; j < numArgs; j++) {
				bw = SMTFloat.randomBitWidth(r, fpMode);
				operandTypes.add (new FloatType (bw));
			}
			bw = SMTFloat.randomBitWidth(r, fpMode);
			resultType = new FloatType (bw);
			sig = new Signature (operandTypes, resultType);
			funcs.add (new UFunc (name, sig));
			builder.append("(declare-fun ");
			//builder.append (":extrafuns ((");
			builder.append (name);
			builder.append(" (");
			for (int j = 0; j < numArgs; j++) {
				if(j != 0) builder.append (" ");
				builder.append (operandTypes.get(j).toString());
			}
			builder.append (") ");
			builder.append (resultType.toString());
			builder.append (")\n");
		}
		System.out.print (builder.toString());
		return numFuncs;
	}

	/*----------------------------------------------------------------------------*/
	/* Main layer                                                                 */
	/*----------------------------------------------------------------------------*/

	private static String wrapEqualBW (Random r, SMTNode n1, SMTNode n2){
		int n1bw;
		int n2bw;
		int ext;
		StringBuilder builder;

		assert (n1 != null);
		assert (n2 != null);
		assert (n1.getType() instanceof FloatType);
		assert (n2.getType() instanceof FloatType);

		n1bw = (((FloatType) n1.getType()).bits);
		n2bw = (((FloatType) n2.getType()).bits);
		builder = new StringBuilder();
		if (n1bw == n2bw) {
			builder.append (n1.getName());
			builder.append (" ");
			builder.append (n2.getName());
		} else if (n1bw < n2bw){
			ext = n2bw - n1bw;
			if (r.nextBoolean())
				builder.append ("(zero_extend[");
			else
				builder.append ("(sign_extend[");
			builder.append (ext);
			builder.append ("] ");
			builder.append (n1.getName());
			builder.append (") ");
			builder.append (n2.getName());
		} else {
			assert (n2bw < n1bw);
			ext = n1bw - n2bw;
			builder.append (n1.getName());
			builder.append (" ");
			if (r.nextBoolean())
				builder.append ("(zero_extend[");
			else
				builder.append ("(sign_extend[");
			builder.append (ext);
			builder.append ("] ");
			builder.append (n2.getName());
			builder.append (")"); 
		}
		return builder.toString();
	}

	private static String adaptBW (Random r, SMTNode n, int bw){
		FloatType type;
		int diff, upper, lower;
		StringBuilder builder;

		assert (r != null);
		assert (n != null);
		assert (n.getType() instanceof FloatType);
		assert (bw > 0);

		type = (FloatType) n.getType();
		builder = new StringBuilder();
		if (type.bits == bw){
			builder.append (n.getName());
		} else if (type.bits < bw) {
			diff = bw - type.bits;
			if (r.nextBoolean())
				builder.append ("(zero_extend[");
			else
				builder.append ("(sign_extend[");
			builder.append (diff);
			builder.append ("] ");
			builder.append (n.getName());
			builder.append (")");
		} else {
			assert (type.bits > bw);
			diff = type.bits - bw;
			lower = r.nextInt(diff + 1);
			upper = lower + bw - 1;
			assert (upper - lower + 1 == bw);
			assert (upper >= 0);
			assert (upper >= lower);
			assert (upper < type.bits);
			builder.append ("(extract[");
			builder.append (upper);
			builder.append (":");
			builder.append (lower);
			builder.append ("] ");
			builder.append (n.getName());
			builder.append (")");
		}
		return builder.toString();
	}

	private static int generateFPLayer(Random r, List<SMTNode> nodes, FPRoundMode rounding,  List<UFunc> uFuncs,
			List<UPred> uPreds, int minRefs) throws Exception {
		// TODO: Main layer for FP [Least complete task]
		int oldSize, upper, lower, maxRep, rep, ext, rotate, pos, tmp;
		int sizeOpTypes, n1BW, n2BW, n3BW, resBW = 0;
		int sizeUFuncs, sizeUPreds;
		SMTNodeKind kind;
		EnumSet<SMTNodeKind> kindSet;
		SMTNodeKind []kinds;
		SMTNode []todoNodesArray;
		UFunc []todoUFuncsArray;
		UPred []todoUPredsArray;
		String name;
		UFunc uFunc;
		UPred uPred;
		Signature sig;
		HashMap<SMTNode, Integer> todoNodes; 
		HashMap<UFunc, Integer> todoUFuncs; 
		HashMap<UPred, Integer> todoUPreds; 
		SMTNode n1, n2, n3, tmpNode;
		FloatType curType;
		List<SMTType> operandTypes;
		StringBuilder builder;

		kindSet = EnumSet.range(SMTNodeKind.PLUS, SMTNodeKind.PLUS);
		kinds = kindSet.toArray(new SMTNodeKind[0]);

		oldSize = nodes.size();

		if (!uFuncs.isEmpty())
			kindSet.add (SMTNodeKind.UFUNC);
		if (!uPreds.isEmpty())
			kindSet.add (SMTNodeKind.UPRED);

		todoNodes = new HashMap<SMTNode, Integer>();
		for (int i = 0; i < oldSize; i++)
			todoNodes.put (nodes.get(i), new Integer(0));

		todoUFuncs = new HashMap<UFunc, Integer>();
		sizeUFuncs = uFuncs.size();
		for (int i = 0; i < sizeUFuncs; i++)
			todoUFuncs.put (uFuncs.get(i), new Integer(0));

		todoUPreds = new HashMap<UPred, Integer>();
		sizeUPreds = uPreds.size();
		for (int i = 0; i < sizeUPreds; i++)
			todoUPreds.put (uPreds.get(i), new Integer(0));

		builder = new StringBuilder();
		while (!todoNodes.isEmpty() || !todoUFuncs.isEmpty() ||
				!todoUPreds.isEmpty()){
			name = "?e" + SMTNode.getNodeCtr();
			//builder.append ("(let (");
			builder.append("(declare-const ");
			builder.append (name);
			builder.append(" Float32"); /* TODO: hard-coded Float32 */
			builder.append (")\n");

			/* increase probability that ufunc or upred is selected
			 * if todo list is not empty */
			if (!todoUFuncs.isEmpty() && r.nextBoolean())
				kind = SMTNodeKind.UFUNC;
			else if (!todoUPreds.isEmpty() && r.nextBoolean())
				kind = SMTNodeKind.UPRED;
			else
				kind = kinds[r.nextInt (kinds.length)];

			// Get first node
			n1 = nodes.get(r.nextInt(nodes.size()));

			builder.append("(assert (= " + name + " (");
			
			switch(kind.arity){
			case 2:
				n2 = nodes.get(r.nextInt(nodes.size()));
				assert (n2.getType() instanceof FloatType);
				n2BW = ((FloatType)n2.getType()).bits;

				switch(kind)
				{
				case PLUS:
					builder.append(kind.string);
					builder.append(" ");
					builder.append("roundTowardZero");
					builder.append(" ");
					builder.append(n1.getName());
					builder.append(" ");
					builder.append(n2.getName());

					updateNodeRefs (todoNodes, n1, minRefs);
					updateNodeRefs (todoNodes, n2, minRefs);
					break;
				default:
					throw new Exception("Missing kind?");
				} // End kind switch for arity == 2
				break;
				
			default:
				assert(kind.arity == -1);
				switch(kind){					
				case UFUNC:
					if (!todoUFuncs.isEmpty() && r.nextBoolean()) {
						todoUFuncsArray = todoUFuncs.keySet().toArray (new UFunc[0]);
						uFunc = todoUFuncsArray[r.nextInt(todoUFuncsArray.length)];
					} else {
						uFunc = uFuncs.get(r.nextInt(sizeUFuncs));
					}
					updateFuncRefs (todoUFuncs, uFunc, minRefs);
					//builder.append (uFunc.getName());
					sig = uFunc.getSignature();
					operandTypes = sig.getOperandTypes();
					sizeOpTypes = operandTypes.size();
					assert (sizeOpTypes > 0);
					curType = (FloatType) operandTypes.get(0);
					builder.append (" ");
					builder.append (adaptBW (r, n1, curType.getWidth()));
					updateNodeRefs (todoNodes, n1, minRefs);
					for (int i = 1; i < sizeOpTypes; i++) {
						n2 = nodes.get(r.nextInt(nodes.size()));
						assert (n2.getType() instanceof FloatType);
						assert (operandTypes.get(i) instanceof FloatType);
						curType = (FloatType) operandTypes.get(i);
						builder.append (" ");
						builder.append (adaptBW (r, n2, curType.getWidth()));
						updateNodeRefs (todoNodes, n2, minRefs);
					}
					assert (sig.getResultType() instanceof FloatType);
					curType = (FloatType) sig.getResultType();
					resBW = curType.getWidth();
					break;
				case UPRED:
					if (!todoUPreds.isEmpty() && r.nextBoolean()) {
						todoUPredsArray = todoUPreds.keySet().toArray (new UPred[0]);
						uPred = todoUPredsArray[r.nextInt(todoUPredsArray.length)];
					} else {
						uPred = uPreds.get(r.nextInt(sizeUPreds));
					}
					updatePredRefs (todoUPreds, uPred, minRefs);
					builder.append ("ite (");
					builder.append (uPred.getName());
					sig = uPred.getSignature();
					operandTypes = sig.getOperandTypes();
					sizeOpTypes = operandTypes.size();
					assert (sizeOpTypes > 0);
					curType = (FloatType) operandTypes.get(0);
					builder.append (" ");
					builder.append (adaptBW (r, n1, curType.getWidth()));
					updateNodeRefs (todoNodes, n1, minRefs);
					for (int i = 1; i < sizeOpTypes; i++) {
						n2 = nodes.get(r.nextInt(nodes.size()));
						assert (n2.getType() instanceof FloatType);
						assert (operandTypes.get(i) instanceof FloatType);
						curType = (FloatType) operandTypes.get(i);
						builder.append (" ");
						builder.append (adaptBW (r, n2, curType.getWidth()));
						updateNodeRefs (todoNodes, n2, minRefs);
					}
					//builder.append (") bv1[1] bv0[1]");
					builder.append(") ");
					builder.append(nodes.get(r.nextInt(nodes.size())).name + " ");
					builder.append(nodes.get(r.nextInt(nodes.size())).name);
					assert (sig.getResultType() == BoolType.boolType);
					resBW = 1;
					break;
				default:
					assert (kind == SMTNodeKind.DISTINCT);
					n2 = nodes.get(r.nextInt(nodes.size()));
					assert (n2.getType() instanceof FloatType);
					n2BW = ((FloatType) n2.getType()).bits;
					builder.append ("ite (");
					builder.append (kind.getString());
					builder.append (" ");
					builder.append (wrapEqualBW (r, n1, n2));
					builder.append (") bv1[1] bv0[1]");
					resBW = 1;
					updateNodeRefs (todoNodes, n1, minRefs);
					updateNodeRefs (todoNodes, n2, minRefs);
					break;
				}					
			} // End arity switch

			builder.append (")))\n");
			//assert (resBW <= maxBW); // TODO check bit widths
			nodes.add (new SMTNode (new FloatType(32), name));			
		} // End while loop

		System.out.print (builder.toString());
		assert (nodes.size() - oldSize > 0);
		return nodes.size() - oldSize;
	}

	/*----------------------------------------------------------------------------*/
	/* Predicate Layer                                                            */
	/*----------------------------------------------------------------------------*/

	private static int generateFPPredicateLayer(Random r, List<SMTNode> fpNodes,
			List<SMTNode> boolNodes,
			int minRefs, 
			List<UPred> uPreds) {
		//TODO: Build predicate layer for FP
		SMTNodeKind kind;
		EnumSet<SMTNodeKind> kindSet;
		SMTNodeKind [] kinds;
		String name;
		HashMap<SMTNode, Integer> todoNodes; 
		HashMap<UPred, Integer> todoUPreds; 
		UPred []todoUPredsArray;
		UPred uPred;
		SMTNode n1, n2;
		int oldSize, sizeBVNodes, sizeOpTypes, sizeUPreds;
		Signature sig;
		StringBuilder builder;
		List<SMTType> operandTypes;
		FloatType curType;

		assert (fpNodes != null);
		assert (!fpNodes.isEmpty());
		assert (boolNodes != null);
		assert (minRefs > 0);

		kindSet = EnumSet.range(SMTNodeKind.AND, SMTNodeKind.OR);
		kinds = kindSet.toArray(new SMTNodeKind[0]);

		todoNodes = new HashMap<SMTNode, Integer>();
		for (int i = 0; i < fpNodes.size(); i++)
			todoNodes.put (fpNodes.get(i), new Integer(0));

		todoUPreds = new HashMap<UPred, Integer>();
		sizeUPreds = uPreds.size();
		for (int i = 0; i < sizeUPreds; i++)
			todoUPreds.put (uPreds.get(i), new Integer(0));

		builder = new StringBuilder();
		oldSize = boolNodes.size();
		sizeBVNodes = fpNodes.size();
		while (!todoNodes.isEmpty() || !todoUPreds.isEmpty()){
			name = "$e" + SMTNode.getNodeCtr();
			//builder.append ("(flet (");
			builder.append("(declare-const ");
			builder.append (name);
			builder.append (" Bool)\n");
			builder.append("(assert (= " + name + " (");
			/* increase probability to select upred
			 * if todo list ist not empty */
			if (!todoUPreds.isEmpty() && r.nextBoolean())
				kind = SMTNodeKind.UPRED;
			else 
				kind = kinds[r.nextInt (kinds.length)];
			assert (kind.arity == 2 || kind.arity == -1);
			if (kind == SMTNodeKind.UPRED) {
				if (!todoUPreds.isEmpty() && r.nextBoolean()) {
					todoUPredsArray = todoUPreds.keySet().toArray (new UPred[0]);
					uPred = todoUPredsArray[r.nextInt(todoUPredsArray.length)];
				} else {
					uPred = uPreds.get(r.nextInt(sizeUPreds));
				}
				updatePredRefs (todoUPreds, uPred, minRefs);
				builder.append (uPred.getName());
				sig = uPred.getSignature();
				operandTypes = sig.getOperandTypes();
				sizeOpTypes = operandTypes.size();
				assert (sizeOpTypes > 0);
				for (int i = 0; i < sizeOpTypes; i++) {
					n1 = fpNodes.get(r.nextInt(sizeBVNodes));
					assert (n1.getType() instanceof FloatType);
					assert (operandTypes.get(i) instanceof FloatType);
					curType = (FloatType) operandTypes.get(i);
					builder.append (" ");
					builder.append (adaptBW (r, n1, curType.getWidth()));
					updateNodeRefs (todoNodes, n1, minRefs);
				}
				assert (sig.getResultType() == BoolType.boolType);
			} else {
				n1 = fpNodes.get(r.nextInt(sizeBVNodes));
				assert (n1.getType() instanceof FloatType);
				n2 = fpNodes.get(r.nextInt(sizeBVNodes));
				assert (n2.getType() instanceof FloatType);
				builder.append (kind.getString());
				builder.append (" ");
				builder.append (wrapEqualBW (r, n1, n2));
				updateNodeRefs (todoNodes, n1, minRefs);
				updateNodeRefs (todoNodes, n2, minRefs);
			}
			builder.append (")))\n");
			boolNodes.add (new SMTNode (BoolType.boolType, name));
		}
		System.out.print (builder.toString());
		assert (boolNodes.size() - oldSize > 0);
		return boolNodes.size() - oldSize;
	}


	/*----------------------------------------------------------------------------*/
	/* Boolean Layer                                                              */
	/*----------------------------------------------------------------------------*/

	private static int generateBooleanLayer (Random r, List<SMTNode> nodes){
		int generated = 0;
		SMTNode n1, n2, n3;
		SMTNodeKind [] kinds;
		SMTNodeKind [] kindsNoIfThenElse;
		SMTNodeKind kind;
		EnumSet<SMTNodeKind> kindSet;
		String name;
		StringBuilder builder;

		assert (r != null);
		assert (nodes != null);
		assert (!nodes.isEmpty());

		kindSet = EnumSet.range (SMTNodeKind.AND, SMTNodeKind.IFF);
		kindSet.add (SMTNodeKind.NOT);
		kindsNoIfThenElse = kindSet.toArray(new SMTNodeKind[0]);
		kindSet.add (SMTNodeKind.IF_THEN_ELSE);
		kinds = kindSet.toArray(new SMTNodeKind[0]);

		builder = new StringBuilder();
		while (nodes.size() > 1){
			name = "$e" + SMTNode.getNodeCtr();
			//builder.append ("(flet (");
			
			builder.append("(declare-const " + name + " Bool)\n");
			
			builder.append("(assert (= " + name + " (");
			n1 = nodes.get(r.nextInt(nodes.size()));
			assert (n1.getType() == BoolType.boolType);

			n2 = n3 = null;
			if (nodes.size() >= 3)
				kind = kinds[r.nextInt(kinds.length)];
			else
				kind = kindsNoIfThenElse[r.nextInt(kindsNoIfThenElse.length)];
			switch (kind) {
			case NOT:
				builder.append (SMTNodeKind.NOT.getString());
				builder.append (" ");
				builder.append (n1.getName());
				break;
			case IF_THEN_ELSE:
				assert (nodes.size() >= 3);
				n2 = nodes.get(r.nextInt(nodes.size()));
				assert (n2.getType() == BoolType.boolType);
				n3 = nodes.get(r.nextInt(nodes.size()));
				assert (n3.getType() == BoolType.boolType);
				builder.append (SMTNodeKind.IF_THEN_ELSE.getString());
				builder.append (" ");
				builder.append (n1.getName());
				builder.append (" ");
				builder.append (n2.getName());
				builder.append (" ");
				builder.append (n3.getName());
				break;
			default:
				/* binary operators */
				n2 = nodes.get(r.nextInt(nodes.size()));
				assert (n2.getType() == BoolType.boolType);
				builder.append (kind.getString());
				builder.append (" ");
				builder.append (n1.getName());
				builder.append (" ");
				builder.append (n2.getName());
				break;
			}
			builder.append (")))\n");
			generated++;
			nodes.add (new SMTNode (BoolType.boolType, name));
			nodes.remove (n1);
			if (n2 != null)
				nodes.remove (n2);
			if (n3 != null)
				nodes.remove (n3);
		}
		System.out.print (builder.toString());

		return generated;
	}

	protected static int generateBooleanTopOp (List<SMTNode> nodes, String op){

		SMTNode cur;
		String name;
		StringBuilder builder;

		assert (nodes != null);
		assert (!nodes.isEmpty());
		assert (op != null);

		if (nodes.size() == 1)
			return 0;

		name = "$e" + SMTNode.getNodeCtr();
		builder = new StringBuilder(); 
		builder.append ("(flet (");
		builder.append (name);
		builder.append (" \n");
		builder.append ("(");
		builder.append (op);
		builder.append ("\n");
		for (int i = 0; i < nodes.size(); i++){
			cur = nodes.get(i);
			assert (cur.getType() == BoolType.boolType);
			builder.append (" ");
			builder.append (cur.getName());
			builder.append ("\n");
		}
		nodes.clear();
		nodes.add (new SMTNode (BoolType.boolType, name));
		builder.append ("))\n");
		System.out.print (builder.toString());
		return 1;
	}

	private static int generateBooleanTopAnd (List<SMTNode> nodes){

		assert (nodes != null);
		assert (!nodes.isEmpty());
		return generateBooleanTopOp (nodes, SMTNodeKind.AND.getString());
	}

	private static int generateBooleanTopOr (List<SMTNode> nodes){

		assert (nodes != null);
		assert (!nodes.isEmpty());
		return generateBooleanTopOp (nodes, SMTNodeKind.OR.getString());
	}

	private static int generateBooleanCNF (Random r, List<SMTNode> nodes, 
			double factor){
		SMTNode cur;
		String name;
		int numClauses;
		StringBuilder builder;

		assert (r != null);
		assert (nodes != null);
		assert (!nodes.isEmpty());
		assert (factor >= 0.0);

		if (nodes.size() == 1)
			return 0;

		numClauses = (int) (nodes.size() * factor);
		if (numClauses <= 1)
			numClauses = 2;

		name = "$e" + SMTNode.getNodeCtr();
		builder = new StringBuilder();
		builder.append ("(flet (");
		builder.append (name);
		builder.append (" \n(and\n");
		for (int i = 0; i < numClauses; i++){
			builder.append (" (or");
			for (int j = 0; j < 3; j++) {
				cur = nodes.get(r.nextInt(nodes.size()));
				assert (cur.getType() == BoolType.boolType);
				builder.append (" ");
				if (r.nextBoolean()) {
					builder.append (cur.getName());
				} else {
					builder.append ("(not ");
					builder.append (cur.getName());
					builder.append (")");
				}
			}
			builder.append (")\n");
		}
		builder.append ("))\n");
		nodes.clear();
		nodes.add (new SMTNode (BoolType.boolType, name));
		System.out.print (builder.toString());
		return 1;
	}

	/*----------------------------------------------------------------------------*/
	/* Main method                                                                */
	/*----------------------------------------------------------------------------*/

	private enum BooleanLayerKind {
		AND,
		OR,
		CNF,
		RANDOM;
	}

	public static void main (String args[]) throws Exception {
		SMTLogic logic = null;
		Random r = null;

		int pars = 1;
		int minRefs = 1;
		int minNumConstsFloat = 1; int maxNumConstsFloat = 1; int numConstsFloat = 0;		
		int minNumVarsFloat = 1; int maxNumVarsFloat = 1; int numVarsFloat = 0;
		int minArgs = 1; int maxArgs = 3;		
		int minNumUFuncsFloat = 0; int maxNumUFuncsFloat = 0; int numUFuncsFloat = 0;
		int minNumUPredsFloat = 0; int maxNumUPredsFloat = 0; int numUPredsFloat = 0;

		//TODO: (main) Add any parameters for FP logic
		// 4 bit pattern indicating support for 16/32/64/128 bit floats is on
		short FPMode = 0;
		FPRoundMode FPRM = FPRoundMode.RNA;

		StringBuilder builder;
		ArrayList<SMTNode> boolNodes = null;

		BooleanLayerKind booleanLayerKind = BooleanLayerKind.RANDOM;

		logic = SMTLogic.stringToLogic.get("QF_FP");

		// TODO: (main) define default FP values
		FPMode = 0b0100; // only use 32-bit floats (IEEE binary32) by default (right now it is set to ALL)
		minNumVarsFloat = 1; maxNumVarsFloat = 1;
		minNumUFuncsFloat = 1; maxNumUFuncsFloat = 1;
		minNumUPredsFloat = 1; maxNumUPredsFloat = 1;
		minNumConstsFloat = 1; maxNumConstsFloat = 1;
		minArgs = 1; maxArgs = 3;

		// TODO: pull these out into separate flag parsing class
		HashMap<String, Object> options = Options.parseArgs(args);


		if (r == null) /* seed has not been set */
			r = new Random();

		assert (minRefs >= 1);

		// TODO: (main) Add FP case for setting parameters and verifying they are in range
		assert(FPMode > 0 && FPMode < 16);
		assert (minArgs > 0); assert (maxArgs > 0);
		assert(minNumVarsFloat > 0); assert(maxNumVarsFloat > 0);
		assert (minNumUFuncsFloat >= 0); assert (maxNumUFuncsFloat >= 0);
		assert (minNumUPredsFloat >= 0); assert (maxNumUPredsFloat >= 0);
		assert (minNumConstsFloat >= 0); assert (maxNumConstsFloat >= 0);

		//checkMinMax(minNumVarsFloat, maxNumVarsFloat, "float variables");
		//checkMinMax(minNumConstsFloat, maxNumConstsFloat, "float constants");
		//checkMinMax(minNumUFuncsFloat, maxNumUFuncsFloat, "uninterpreted float functions");
		//checkMinMax(minNumUPredsFloat, maxNumUPredsFloat, "uninterpreted float predicates");

		numVarsFloat = selectRandValRange(r, minNumVarsFloat, maxNumVarsFloat);
		numConstsFloat = selectRandValRange(r, minNumConstsFloat, maxNumConstsFloat);
		numUFuncsFloat = selectRandValRange(r, minNumUFuncsFloat, maxNumUFuncsFloat);
		numUPredsFloat = selectRandValRange(r, minNumUPredsFloat, maxNumUPredsFloat);

		boolNodes = new ArrayList<SMTNode>();
		assert (r != null);
		assert (logic != null);
		//System.out.println ("(benchmark fuzzsmt");
		//System.out.println (":logic " + logic.toString());
		//System.out.println (":status unknown");

		// TODO: (main) Add FP case for generating first three layers
		ArrayList<SMTNode> fpNodes = new ArrayList<SMTNode>();
		ArrayList<UFunc> fpuFuncs = new ArrayList<UFunc>();
		ArrayList<UPred> fpuPreds = new ArrayList<UPred>();

		generateUFuncsFP(r, fpuFuncs, numUFuncsFloat, minArgs, maxArgs, FPMode);
		generateUPredsFP(r, fpuPreds, numUPredsFloat, minArgs, maxArgs, FPMode);

		pars += generateFPVars(r, fpNodes, numVarsFloat, FPMode);
		//System.out.println(":formula");
		pars += generateFPConsts(r, fpNodes, numConstsFloat, FPMode);
		pars += generateFPLayer(r, fpNodes, FPRM, fpuFuncs, fpuPreds, minRefs);
		pars += generateFPPredicateLayer(r, fpNodes, boolNodes, minRefs, fpuPreds);			

		/* generate boolean layer */
		assert (boolNodes.size() > 0);
		switch (booleanLayerKind) {
		case RANDOM:
			pars += generateBooleanLayer (r, boolNodes);
			break;
		case AND:
			pars += generateBooleanTopAnd (boolNodes);
			break;
		case OR:
			pars += generateBooleanTopOr (boolNodes);
			break;
		case CNF:
			pars += generateBooleanCNF (r, boolNodes, 1.0); // TODO support factor as CLA again?
			break;
		}
		assert (boolNodes.size() == 1);
		assert (boolNodes.get(0).getType() == BoolType.boolType);
		//System.out.println (boolNodes.get(0).getName());
		System.out.println("(check-sat)\n");
		
		System.exit (0);
	}
}