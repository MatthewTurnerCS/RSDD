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
import java.math.*;

public class FuzzSMT {

	/*----------------------------------------------------------------------------*/
	/* Auxillary                                                                  */
	/*----------------------------------------------------------------------------*/

	private enum RelCompMode {
		OFF,
		EQ,
		FULL;
	}

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
		assert (r != null);
		assert (min >= 0);
		assert (max >= 0);
		assert (max >= min);
		result = r.nextInt(max - min + 1) + min;
		assert (result >= min);
		assert (result <= max);
		return result;
	}

	private static void updateStringRefs (HashMap<String, Integer> map, 
			String string, int minRefs){
		Integer refs;

		assert (map != null);
		assert (string != null);
		assert (minRefs > 0);

		refs = map.get(string);
		if (refs != null) {
			refs = new Integer (refs.intValue() + 1);
			if (refs.intValue() >= minRefs)
				map.remove(string);
			else
				map.put (string, refs);
		}
	}


	private static void updateNodeRefs (HashMap<SMTNode, Integer> map, 
			SMTNode node, int minRefs){
		Integer refs;

		assert (map != null);
		assert (node != null);
		assert (minRefs > 0);

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

		assert (map != null);
		assert (uFunc != null);
		assert (minRefs > 0);

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

		assert (map != null);
		assert (uPred != null);
		assert (minRefs > 0);

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

	private static int generateVarsOfOneType (List<SMTNode> nodes, int numVars, 
			SMTType type){
		String name;
		StringBuilder builder;
		
		assert (nodes != null);
		assert (type != null);
		assert (numVars >= 0);

		builder = new StringBuilder();
		for (int i = 0; i < numVars; i++) {
			name = "v" + SMTNode.getNodeCtr();
			builder.append (":extrafuns ((");
			builder.append (name);
			builder.append (" ");
			builder.append (type.toString());
			builder.append ("))\n");
			nodes.add (new SMTNode (type, name));
		}
		System.out.print (builder.toString());
		return numVars;
	}

	private static int generateFPVars (Random r, List<SMTNode> nodes, int numVars, short fpMode) {
		//TODO: Build input layer for FP (vars)
		assert (nodes != null);
		assert (numVars >= 0);
		StringBuilder builder = new StringBuilder();
		String name;
		for(int i=0; i < numVars; i++){
			name = "v" + SMTNode.getNodeCtr();
			int bw = SMTFloat.randomBitWidth(r, fpMode);
			builder.append (":extrafuns ((");
			builder.append (name);
			builder.append (" Float[");
			builder.append (bw);
			builder.append ("]))\n");
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

			builder.append ("(let (");
			builder.append (name);
			builder.append (" ");
			builder.append (floatConst.toString());
			builder.append (")\n");
			nodes.add (new SMTNode (new FloatType(bw), name));
		}
		System.out.print (builder.toString());

		return numConsts;
	}

	private static int generateUTypes (List<SMTType> types, int numUTypes){
		String name;
		StringBuilder builder;

		assert (types != null);
		assert (numUTypes > 0);

		builder = new StringBuilder();
		for (int i = 0; i < numUTypes; i++) {
			name = "S" + i;
			types.add (new UType (name));
			builder.append (":extrasorts (");
			builder.append (name);
			builder.append (")\n");
		}
		System.out.print (builder.toString());
		return numUTypes;
	}

	private static int generateUVars (List<SMTType> sorts, List<SMTNode> nodes,
			int numVars) {
		int generated = 0;
		int sizeSorts;

		assert (sorts != null);
		assert (sorts.size() > 0);
		assert (nodes != null);

		sizeSorts = sorts.size();
		for (int i = 0; i < sizeSorts; i++)
			generated += generateVarsOfOneType (nodes, numVars, sorts.get(i));

		assert (generated == sizeSorts * numVars);
		return generated;
	}

	private static int generateUFuncs (Random r, List<SMTType> sorts, 
			List<UFunc> funcs, int minNumFuncs, 
			int minArgs, int maxArgs) {
		int generated = 0;
		int numArgs, sizeSorts;
		Signature sig;
		ArrayList<SMTType> operandTypes;
		SMTType resultType, cur;
		HashSet<SMTType> todoResult, todoArg;
		String name;
		StringBuilder builder;

		assert (r != null);
		assert (sorts != null);
		assert (sorts.size() > 0);
		assert (funcs != null);
		assert (minNumFuncs > 0);
		assert (minArgs >= 1);
		assert (maxArgs >= minArgs);

		sizeSorts = sorts.size();
		/* each sort must be used as return type at least once */
		todoResult = new HashSet<SMTType>();
		for (int i = 0; i < sizeSorts; i++)
			todoResult.add (sorts.get(i));

		/* each sort must be used as argument type at least once */
		todoArg = new HashSet<SMTType>();
		for (int i = 0; i < sizeSorts; i++)
			todoArg.add (sorts.get(i));

		builder = new StringBuilder();
		while (!todoResult.isEmpty() || !todoArg.isEmpty() ||
				generated < minNumFuncs){
			name = "f" + UFunc.getFuncsCtr();
			numArgs = selectRandValRange (r, minArgs, maxArgs); 
			assert (numArgs >= minArgs);
			assert (numArgs <= maxArgs);
			operandTypes = new ArrayList<SMTType>(numArgs);
			for (int i = 0; i < numArgs; i++) {
				cur = sorts.get(r.nextInt(sizeSorts));
				operandTypes.add (cur);
				if (todoArg.contains (cur))
					todoArg.remove(cur);
			}
			resultType = sorts.get(r.nextInt(sizeSorts));
			if (todoResult.contains (resultType))
				todoResult.remove (resultType);
			sig = new Signature (operandTypes, resultType);
			funcs.add (new UFunc (name, sig));
			builder.append (":extrafuns ((");
			builder.append (name);
			for (int i = 0; i < numArgs; i++) {
				builder.append (" ");
				builder.append (operandTypes.get(i).toString());
			}
			builder.append (" ");
			builder.append (resultType.toString());
			builder.append ("))\n");
			generated++;
		}
		System.out.print (builder.toString());
		assert (generated > 0);
		return generated;
	}

	private static int generateUPreds (Random r, List<SMTType> sorts, 
			List<UPred> preds, int minNumPreds, 
			int minArgs, int maxArgs) throws Exception {
    throw new Exception("generateUPreds was called D:?");
		// int generated = 0;
		// int numArgs, sizeSorts;
		// Signature sig;
		// ArrayList<SMTType> operandTypes;
		// SMTType cur;
		// HashSet<SMTType> todo;
		// String name;
		// StringBuilder builder;

		// assert (r != null);
		// assert (sorts != null);
		// assert (sorts.size() > 0);
		// assert (preds != null);
		// assert (minNumPreds > 0);
		// assert (minArgs >= 1);
		// assert (maxArgs >= minArgs);

		// /* each sort must be used as argument type at least once */
		// sizeSorts = sorts.size();
		// todo = new HashSet<SMTType>();
		// for (int i = 0; i < sizeSorts; i++)
		// 	todo.add (sorts.get(i));

		// builder = new StringBuilder();
		// while (!todo.isEmpty() || generated < minNumPreds){
		// 	name = "p" + UPred.getPredsCtr();
		// 	numArgs = selectRandValRange (r, minArgs, maxArgs);
		// 	assert (numArgs >= minArgs);
		// 	assert (numArgs <= maxArgs);
		// 	operandTypes = new ArrayList<SMTType>(numArgs);
		// 	for (int i = 0; i < numArgs; i++) {
		// 		cur = sorts.get(r.nextInt(sizeSorts));
		// 		if (todo.contains (cur))
		// 			todo.remove (cur);
		// 		operandTypes.add (cur);
		// 	}
		// 	sig = new Signature (operandTypes, BoolType.boolType);
		// 	preds.add (new UPred (name, sig));
		// 	builder.append (":extrapreds ((");
		// 	builder.append (name);
		// 	for (int i = 0; i < numArgs; i++) {
		// 		builder.append (" ");
		// 		builder.append (operandTypes.get(i).toString());
		// 	}
		// 	builder.append ("))\n");
		// 	generated++;
		// }
		// System.out.print (builder.toString());
		// assert (generated > 0);
		// return generated;
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
			preds.add (new UPred (name, sig));
			builder.append (":extrapreds ((");
			builder.append (name);
			for (int j = 0; j < numArgs; j++) {
				builder.append (" ");
				builder.append (operandTypes.get(j).toString());
			}
			builder.append ("))\n");
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
			builder.append (":extrafuns ((");
			builder.append (name);
			for (int j = 0; j < numArgs; j++) {
				builder.append (" ");
				builder.append (operandTypes.get(j).toString());
			}
			builder.append (" ");
			builder.append (resultType.toString());
			builder.append ("))\n");
		}
		System.out.print (builder.toString());
		return numFuncs;
	}

	/*----------------------------------------------------------------------------*/
	/* Main layer                                                                 */
	/*----------------------------------------------------------------------------*/

	private static int generateFPLayer(Random r, List<SMTNode> nodes, FPRoundMode rounding, Object other_args) {
		// TODO: Main layer for FP [Least complete task]
		int oldSize = nodes.size();
		nodes.add(new SMTNode(new FloatType(32), "Test"));
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
		//FloatType curType;

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
			builder.append ("(flet (");
			builder.append (name);
			builder.append (" (");
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
					//curType = (FloatType) operandTypes.get(i);
					//builder.append (" ");
					//builder.append (adaptBW (r, n1, curType.getWidth()));
					updateNodeRefs (todoNodes, n1, minRefs);
				}
				assert (sig.getResultType() == BoolType.boolType);
			} else {
				n1 = fpNodes.get(r.nextInt(sizeBVNodes));
				assert (n1.getType() instanceof FloatType);
				n2 = fpNodes.get(r.nextInt(sizeBVNodes));
				assert (n2.getType() instanceof FloatType);
				//builder.append (kind.getString());
				//builder.append (" ");
				//builder.append (wrapEqualBW (r, n1, n2));
				updateNodeRefs (todoNodes, n1, minRefs);
				updateNodeRefs (todoNodes, n2, minRefs);
			}
			builder.append ("))\n");
			boolNodes.add (new SMTNode (BoolType.boolType, name));
		}
		System.out.print (builder.toString());
		assert (boolNodes.size() - oldSize > 0);
		return boolNodes.size() - oldSize;
	}

	private static int generateUPredLayer (Random r, List<SMTNode> nodes, 
			List<SMTNode> boolNodes, 
			List<UPred> preds, int minRefs) {

		int oldSize, sizePreds, sizeOperandTypes;
		String name;
		HashMap<SMTNode, Integer> todoNodes; 
		SMTNode []todoNodesArray;
		HashSet<UPred> todoPreds; 
		UPred pred;
		Signature sig;
		List<SMTType> operandTypes;
		SMTType curType;
		StringBuilder builder;
		SMTNode n1, n2;

		assert (r != null);
		assert (nodes != null);
		assert (nodes.size() > 0);
		assert (boolNodes != null);
		assert (preds != null);
		assert (preds.size() > 0);
		assert (minRefs > 0);

		oldSize = boolNodes.size();
		sizePreds = preds.size();
		/* each predicate should be used at least once */
		todoPreds = new HashSet<UPred>();
		for (int i = 0; i < sizePreds; i++)
			todoPreds.add (preds.get(i));

		todoNodes = new HashMap<SMTNode, Integer>();
		for (int i = 0; i < nodes.size(); i++)
			todoNodes.put (nodes.get(i), new Integer(0));

		builder = new StringBuilder();
		while (!todoNodes.isEmpty() || !todoPreds.isEmpty()){
			name = "$e" + SMTNode.getNodeCtr();
			builder.append ("(flet (");
			builder.append (name);
			builder.append (" (");
			if (r.nextBoolean() || todoNodes.isEmpty()) {
				pred = preds.get (r.nextInt(sizePreds));
				if (todoPreds.contains (pred))
					todoPreds.remove (pred);
				builder.append (pred.getName());
				sig = pred.getSignature();
				operandTypes = sig.getOperandTypes();
				assert (sig.getResultType() == BoolType.boolType);
				sizeOperandTypes = operandTypes.size();
				for (int i = 0; i < sizeOperandTypes; i++){
					builder.append (" ");
					curType = operandTypes.get(i);
					do {
						n1 = nodes.get(r.nextInt(nodes.size()));
					} while (n1.getType() != curType);
					updateNodeRefs (todoNodes, n1, minRefs);
					builder.append (n1.getName());
				}
			} else {
				if (r.nextBoolean())
					builder.append (SMTNodeKind.EQ.getString());
				else
					builder.append (SMTNodeKind.DISTINCT.getString());
				builder.append (" ");
				/* select at least one of the todo nodes,
				 * to prevent blowup because of type incompatibility */
				todoNodesArray = todoNodes.keySet().toArray (new SMTNode[0]);
				n1 = todoNodesArray[r.nextInt(todoNodesArray.length)];
				curType = n1.getType();
				do {
					n2 = nodes.get(r.nextInt(nodes.size()));
				} while (curType != n2.getType());
				builder.append (n1.getName());
				builder.append (" ");
				builder.append (n2.getName());
				updateNodeRefs (todoNodes, n1, minRefs);
				updateNodeRefs (todoNodes, n2, minRefs);
			}
			builder.append ("))\n");
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
			builder.append ("(flet (");
			builder.append (name);
			builder.append (" (");
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
			builder.append ("))\n");
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

	private static void printErrAndExit (String string) {
		assert (string != null);
		System.err.println (string);
		System.exit (1);
	}

	private static void checkMinMax (int min, int max, String str){
		assert (min >= 0);
		assert (max >= 0);
		assert (str != null);
		if (max < min)
			printErrAndExit ("minimum number of " + str + " must be <= maximum");
	}

	private static void printHelpAndExit () {
		System.out.println (Options.usage);
		System.exit (0);
	}

	private static void printVersionAndExit () {
		System.out.println (Options.version);
		System.exit (0);
	}

	private static int parseIntOption (String []args, int pos, int minVal, 
			String errorMsg) {
		int result = 0;

		assert (args != null);
		assert (pos >= 0);
		assert (pos < args.length);
		assert (errorMsg != null);
		if (pos == args.length - 1)
			printErrAndExit ("option argument missing");
		try {
			result = Integer.valueOf(args[pos + 1]).intValue();
		} catch (NumberFormatException nfe) {
			printErrAndExit (errorMsg);
		}
		if (result < minVal)
			printErrAndExit (errorMsg);
		return result;
	}

	private static long parseLongOption (String []args, int pos, long minVal, 
			String errorMsg) {
		long result = 0l;

		assert (args != null);
		assert (pos >= 0);
		assert (pos < args.length);
		assert (errorMsg != null);
		if (pos == args.length - 1)
			printErrAndExit ("option argument missing");
		try {
			result = Long.valueOf(args[pos + 1]).longValue();
		} catch (NumberFormatException nfe) {
			printErrAndExit (errorMsg);
		}
		if (result < minVal)
			printErrAndExit (errorMsg);
		return result;
	}

	private static double parseDoubleOption (String []args, int pos, double minVal, 
			String errorMsg) {
		double result = 0.0;

		assert (args != null);
		assert (pos >= 0);
		assert (pos < args.length);
		assert (errorMsg != null);
		if (pos == args.length - 1)
			printErrAndExit ("option argument missing");
		try {
			result = Double.valueOf(args[pos + 1]).doubleValue();
		} catch (NumberFormatException nfe) {
			printErrAndExit (errorMsg);
		}
		if (result < minVal)
			printErrAndExit (errorMsg);
		return result;
	}

	public static void main (String args[]) {
		SMTLogic logic = null;
		Random r = null;
		int pars = 1;
		int minRefs = 1;
		int minNumConsts = 1;
		int maxNumConsts = 1;
		int numConsts = 0;
		int minNumConstsInt = 1;
		int maxNumConstsInt = 1;
		int minNumConstsFloat = 1;
		int maxNumConstsFloat = 1;
		int numConstsFloat = 0;
		int numConstsInt = 0;
		int minNumConstsIntAsReal = 1;
		int maxNumConstsIntAsReal = 1;
		int numConstsIntAsReal = 0;
		int minNumVars = 1;
		int maxNumVars = 1;
		int numVars = 0;
		int minNumVarsInt = 1;
		int maxNumVarsInt = 1;
		int numVarsInt = 0;
		int minNumVarsFloat = 1;
		int maxNumVarsFloat = 1;
		int numVarsFloat = 0;
		int minNumVarsReal = 1;
		int maxNumVarsReal = 1;
		int numVarsReal = 0;
		int minNumArrays = 1;
		int maxNumArrays = 1;
		int numArrays = 0;
		int minNumArrays1 = 0;
		int maxNumArrays1 = 0;
		int numArrays1 = 0;
		int minNumArrays2 = 0;
		int maxNumArrays2 = 0;
		int numArrays2 = 0;
		int minNumReads = 1;
		int maxNumReads = 1;
		int numReads = 0;
		int minNumReadsArray1 = 1;
		int maxNumReadsArray1 = 1;
		int numReadsArray1 = 0;
		int minNumReadsArray2 = 1;
		int maxNumReadsArray2 = 1;
		int numReadsArray2 = 0;
		int minNumWrites = 0;
		int maxNumWrites = 0;
		int numWrites = 0;
		int minNumWritesArray1 = 0;
		int maxNumWritesArray1 = 0;
		int numWritesArray1 = 0;
		int minNumWritesArray2 = 0;
		int maxNumWritesArray2 = 0;
		int numWritesArray2 = 0;
		int minBW = 0;
		int maxBW = 0;
		int minNumExtBool = 0;
		int maxNumExtBool = 0;
		int numExtBool = 0;
		int minNumSorts = 1;
		int maxNumSorts = 1;
		int numSorts = 0;
		int minNumUFuncs = 0;
		int maxNumUFuncs = 0;
		int numUFuncs = 0;
		int minNumUPreds = 0;
		int maxNumUPreds = 0;
		int numUPreds = 0;
		int minArgs = 1;
		int maxArgs = 3;
		int minNumIndices = 1;
		int maxNumIndices = 1;
		int numIndices = 0;
		int minNumElements = 1;
		int maxNumElements = 1;
		int numElements = 0;
		int minNumQFormulasInt = 0;
		int maxNumQFormulasInt = 0;
		int numQFormulasInt = 0;
		int minNumQFormulasReal = 0;
		int maxNumQFormulasReal = 0;
		int numQFormulasReal = 0;
		int minNumQFormulasArray = 0;
		int maxNumQFormulasArray = 0;
		int numQFormulasArray = 0;
		int minNumQFormulasArray1 = 0;
		int maxNumQFormulasArray1 = 0;
		int numQFormulasArray1 = 0;
		int minNumQFormulasArray2 = 0;
		int maxNumQFormulasArray2 = 0;
		int numQFormulasArray2 = 0;
		int minQVars = 0;
		int maxQVars = 0;
		int minQNestings = 0;
		int maxQNestings = 0;
		int minNumUFuncsInt = 0;
		int maxNumUFuncsInt = 0;
		int numUFuncsInt = 0;
		int minNumUFuncsFloat = 0;
		int maxNumUFuncsFloat = 0;
		int numUFuncsFloat = 0;
		int minNumUFuncsReal = 0;
		int maxNumUFuncsReal = 0;
		int numUFuncsReal = 0;
		int minNumUFuncsArray = 0;
		int maxNumUFuncsArray = 0;
		int numUFuncsArray = 0;
		int minNumUFuncsArray1 = 0;
		int maxNumUFuncsArray1 = 0;
		int numUFuncsArray1 = 0;
		int minNumUFuncsArray2 = 0;
		int maxNumUFuncsArray2 = 0;
		int numUFuncsArray2 = 0;
		int minNumUPredsInt = 0;
		int maxNumUPredsInt = 0;
		int numUPredsInt = 0;
		int minNumUPredsFloat = 0;
		int maxNumUPredsFloat = 0;
		int numUPredsFloat = 0;
		int minNumUPredsReal = 0;
		int maxNumUPredsReal = 0;
		int numUPredsReal = 0;
		int minNumUPredsArray = 0;
		int maxNumUPredsArray = 0;
		int numUPredsArray = 0;
		int minNumUPredsArray1 = 0;
		int maxNumUPredsArray1 = 0;
		int numUPredsArray1 = 0;
		int minNumUPredsArray2 = 0;
		int maxNumUPredsArray2 = 0;
		int numUPredsArray2 = 0;
		boolean linear = true;
		double factor = 1.0;
		RelCompMode compModeArray = RelCompMode.OFF;
		RelCompMode compModeArray1 = RelCompMode.OFF;
		RelCompMode compModeArray2 = RelCompMode.OFF;

		//TODO: (main) Add any parameters for FP logic
		// 4 bit pattern indicating support for 16/32/64/128 bit floats is on
		short FPMode = 0;
		FPRoundMode FPRM = FPRoundMode.RNA;

		StringBuilder builder;
		ArrayList<SMTNode> boolNodes = null;
		HashMap<SMTNode, SMTNodeKind> BVDivGuards = null;
		BooleanLayerKind booleanLayerKind = BooleanLayerKind.RANDOM;

		if (args.length == 0) {
			System.out.println (Options.usage);
			System.exit (0);
		}

		if (args[0].equals ("-V"))
			printVersionAndExit ();

		if (args[0].equals ("-h"))
			printHelpAndExit ();

		// logic = SMTLogic.stringToLogic.get(args[0]);
		// if (logic == null)
		// 	printHelpAndExit();
    logic = SMTLogic.stringToLogic.get("QF_FP");

    // TODO: (main) define default FP values
    FPMode = 15; // only use 32-bit floats (IEEE binary32) by default (right now it is set to ALL)
    minNumVarsFloat = 1;
    maxNumVarsFloat = 5;
    minNumUFuncsFloat = 1;
    maxNumUFuncsFloat = 5;
    minNumUPredsFloat = 1;
    maxNumUPredsFloat = 5;
    minNumConstsFloat = 1;
    maxNumConstsFloat = 5;
    minArgs = 1;
    maxArgs = 3;

    // TODO: pull these out into separate flag parsing class
		for (int i = 1; i < args.length; i++) {
			String arg = args[i];
			if (arg.charAt(0) == '-') {
				if (arg.equals ("-h")) {
					printHelpAndExit ();
				} else if (arg.equals("-V")) {
					printVersionAndExit ();
				} else if (arg.equals("-x")) {
					compModeArray = RelCompMode.EQ;
				} else if (arg.equals("-x1")) {
					compModeArray1 = RelCompMode.EQ;
				} else if (arg.equals("-x2")) {
					compModeArray2 = RelCompMode.EQ;
				} else if (arg.equals("-bool-random")) {
					booleanLayerKind = BooleanLayerKind.RANDOM;
				} else if (arg.equals("-bool-and")) {
					booleanLayerKind = BooleanLayerKind.AND;
				} else if (arg.equals("-bool-or")) {
					booleanLayerKind = BooleanLayerKind.OR;
				} else if (arg.equals("-seed")) {
					r = new Random (parseLongOption (args, i++, 0l, "invalid seed"));
				} else if (arg.equals("-bool-cnf")) {
					factor = parseDoubleOption (args, i++, 0.0, "invalid CNF factor");
					booleanLayerKind = BooleanLayerKind.CNF;
				} else if (arg.equals("-ref")) {
					minRefs = parseIntOption (args, i++, 1, "invalid minimum number of references");
				} else if (arg.equals("-mv")) {
					minNumVars = parseIntOption (args, i++, 1, "invalid minimum number of variables");
				} else if (arg.equals("-Mv")) {
					maxNumVars = parseIntOption (args, i++, 1, "invalid maximum number of variables");
				} else if (arg.equals("-mvi")) {
					minNumVarsInt = parseIntOption (args, i++, 1, "invalid minimum number of variables of type integer");
				} else if (arg.equals("-Mvi")) {
					maxNumVarsInt = parseIntOption (args, i++, 1, "invalid maximum number of variables of type integer");
				} else if (arg.equals("-mvr")) {
					minNumVarsReal = parseIntOption (args, i++, 1, "invalid minimum number of variables of type real");
				} else if (arg.equals("-Mvr")) {
					maxNumVarsReal = parseIntOption (args, i++, 1, "invalid maximum number of variables of type real");
				} else if (arg.equals("-mc")) {
					minNumConsts = parseIntOption (args, i++, 1, "invalid minimum number of constants");
				} else if (arg.equals("-Mc")) {
					maxNumConsts = parseIntOption (args, i++, 1, "invalid maximum number of constants");
				} else if (arg.equals("-mci")) {
					minNumConstsInt = parseIntOption (args, i++, 1, "invalid minimum number of integer constants");
				} else if (arg.equals("-Mci")) {
					maxNumConstsInt = parseIntOption (args, i++, 1, "invalid maximum number of integer constants");
				} else if (arg.equals("-mcr")) {
					minNumConstsIntAsReal = parseIntOption (args, i++, 1, "invalid minimum number of integer constants in real context");
				} else if (arg.equals("-Mcr")) {
					maxNumConstsIntAsReal = parseIntOption (args, i++, 1, "invalid maximum number of integer constants in real context");
				} else if (arg.equals("-ms")) {
					minNumSorts = parseIntOption (args, i++, 1, "invalid minimum number of sorts");
				} else if (arg.equals("-Ms")) {
					maxNumSorts = parseIntOption (args, i++, 1, "invalid maximum number of sorts");
				} else if (arg.equals("-mf")) {
					minNumUFuncs = parseIntOption (args, i++, 0, "invalid minimum number of uninterpreted functions");
				} else if (arg.equals("-Mf")) {
					maxNumUFuncs = parseIntOption (args, i++, 0, "invalid maximum number of uninterpreted functions");
				} else if (arg.equals("-mfi")) {
					minNumUFuncsInt = parseIntOption (args, i++, 0, "invalid minimum number of uninterpreted integer functions");
				} else if (arg.equals("-Mfi")) {
					maxNumUFuncsInt = parseIntOption (args, i++, 0, "invalid maximum number of uninterpreted integer functions");
				} else if (arg.equals("-mfr")) {
					minNumUFuncsReal = parseIntOption (args, i++, 0, "invalid minimum number of uninterpreted real functions");
				} else if (arg.equals("-Mfr")) {
					maxNumUFuncsReal = parseIntOption (args, i++, 0, "invalid maximum number of uninterpreted real functions");
				} else if (arg.equals("-mfar")) {
					minNumUFuncsArray = parseIntOption (args, i++, 0, "invalid minimum number of uninterpreted array functions");
				} else if (arg.equals("-Mfar")) {
					maxNumUFuncsArray = parseIntOption (args, i++, 0, "invalid maximum number of uninterpreted array functions");
				} else if (arg.equals("-mfar1")) {
					minNumUFuncsArray1 = parseIntOption (args, i++, 0, "invalid minimum number of uninterpreted array1 functions");
				} else if (arg.equals("-Mfar1")) {
					maxNumUFuncsArray1 = parseIntOption (args, i++, 0, "invalid maximum number of uninterpreted array1 functions");
				} else if (arg.equals("-mfar2")) {
					minNumUFuncsArray2 = parseIntOption (args, i++, 0, "invalid minimum number of uninterpreted array2 functions");
				} else if (arg.equals("-Mfar2")) {
					maxNumUFuncsArray2 = parseIntOption (args, i++, 0, "invalid maximum number of uninterpreted array2 functions");
				} else if (arg.equals("-mp")) {
					minNumUPreds = parseIntOption (args, i++, 0, "invalid minimum number of uninterpreted predicates");
				} else if (arg.equals("-Mp")) {
					maxNumUPreds = parseIntOption (args, i++, 0, "invalid maximum number of uninterpreted predicates");
				} else if (arg.equals("-mpi")) {
					minNumUPredsInt = parseIntOption (args, i++, 0, "invalid minimum number of uninterpreted integer predicates");
				} else if (arg.equals("-Mpi")) {
					maxNumUPredsInt = parseIntOption (args, i++, 0, "invalid maximum number of uninterpreted integer predicates");
				} else if (arg.equals("-mpr")) {
					minNumUPredsReal = parseIntOption (args, i++, 0, "invalid minimum number of uninterpreted real predicates");
				} else if (arg.equals("-Mpr")) {
					maxNumUPredsReal = parseIntOption (args, i++, 0, "invalid maximum number of uninterpreted real predicates");
				} else if (arg.equals("-mpar")) {
					minNumUPredsArray = parseIntOption (args, i++, 0, "invalid minimum number of uninterpreted array predicates");
				} else if (arg.equals("-Mpar")) {
					maxNumUPredsArray = parseIntOption (args, i++, 0, "invalid maximum number of uninterpreted array predicates");
				} else if (arg.equals("-mpar1")) {
					minNumUPredsArray1 = parseIntOption (args, i++, 0, "invalid minimum number of uninterpreted array1 predicates");
				} else if (arg.equals("-Mpar1")) {
					maxNumUPredsArray1 = parseIntOption (args, i++, 0, "invalid maximum number of uninterpreted array1 predicates");
				} else if (arg.equals("-mpar2")) {
					minNumUPredsArray2 = parseIntOption (args, i++, 0, "invalid minimum number of uninterpreted array2 predicates");
				} else if (arg.equals("-Mpar2")) {
					maxNumUPredsArray2 = parseIntOption (args, i++, 0, "invalid maximum number of uninterpreted array2 predicates");
				} else if (arg.equals("-ma")) {
					minArgs = parseIntOption (args, i++, 1, "invalid minimum number of arguments");
				} else if (arg.equals("-Ma")) {
					maxArgs = parseIntOption (args, i++, 1, "invalid maximum number of arguments");
				} else if (arg.equals("-mqfi")) {
					minNumQFormulasInt = parseIntOption (args, i++, 0, "invalid minimum number of quantified formulas over integers");
				} else if (arg.equals("-Mqfi")) {
					maxNumQFormulasInt = parseIntOption (args, i++, 0, "invalid maximum number of quantified formulas over integers");
				} else if (arg.equals("-mqfr")) {
					minNumQFormulasReal = parseIntOption (args, i++, 0, "invalid minimum number of quantified formulas over reals");
				} else if (arg.equals("-Mqfr")) {
					maxNumQFormulasReal = parseIntOption (args, i++, 0, "invalid maximum number of quantified formulas over reals");
				} else if (arg.equals("-mqfar")) {
					minNumQFormulasArray = parseIntOption (args, i++, 0, "invalid minimum number of quantified formulas over arrays");
				} else if (arg.equals("-Mqfar")) {
					maxNumQFormulasArray = parseIntOption (args, i++, 0, "invalid maximum number of quantified formulas over arrays");
				} else if (arg.equals("-mqfar1")) {
					minNumQFormulasArray1 = parseIntOption (args, i++, 0, "invalid minimum number of quantified formulas over arrays of type array1");
				} else if (arg.equals("-Mqfar1")) {
					maxNumQFormulasArray1 = parseIntOption (args, i++, 0, "invalid maximum number of quantified formulas over arrays of type array1");
				} else if (arg.equals("-mqfar2")) {
					minNumQFormulasArray2 = parseIntOption (args, i++, 0, "invalid minimum number of quantified formulas over arrays of type array2");
				} else if (arg.equals("-Mqfar2")) {
					maxNumQFormulasArray2 = parseIntOption (args, i++, 0, "invalid maximum number of quantified formulas over arrays of type array2");
				} else if (arg.equals("-mqv")) {
					minQVars = parseIntOption (args, i++, 1, "invalid minimum number of quantified variables");
				} else if (arg.equals("-Mqv")) {
					maxQVars = parseIntOption (args, i++, 1, "invalid maximum number of quantified variables");
				} else if (arg.equals("-mqn")) {
					minQNestings = parseIntOption (args, i++, 0, "invalid minimum number of quantifier nestings");
				} else if (arg.equals("-Mqn")) {
					maxQNestings = parseIntOption (args, i++, 0, "invalid maximum number of quantifier nestings");
				} else if (arg.equals("-mar")) {
					minNumArrays = parseIntOption (args, i++, 1, "invalid minimum number of arrays");
				} else if (arg.equals("-Mar")) {
					maxNumArrays = parseIntOption (args, i++, 1, "invalid maximum number of arrays");
				} else if (arg.equals("-mar1")) {
					minNumArrays1 = parseIntOption (args, i++, 1, "invalid minimum number of arrays of type array1");
				} else if (arg.equals("-Mar1")) {
					maxNumArrays1 = parseIntOption (args, i++, 1, "invalid maximum number of arrays of type array1");
				} else if (arg.equals("-mar2")) {
					minNumArrays2 = parseIntOption (args, i++, 1, "invalid minimum number of arrays of type array2");
				} else if (arg.equals("-Mar2")) {
					maxNumArrays2 = parseIntOption (args, i++, 1, "invalid maximum number of arrays of type array2");
				} else if (arg.equals("-mi")) {
					minNumIndices = parseIntOption (args, i++, 1, "invalid minimum number of indices");
				} else if (arg.equals("-Mi")) {
					maxNumIndices = parseIntOption (args, i++, 1, "invalid maximum number of indices");
				} else if (arg.equals("-me")) {
					minNumElements = parseIntOption (args, i++, 1, "invalid minimum number of elements");
				} else if (arg.equals("-Me")) {
					maxNumElements = parseIntOption (args, i++, 1, "invalid maximum number of elements");
				} else if (arg.equals("-mr")) {
					minNumReads = parseIntOption (args, i++, 1, "invalid minimum number of reads");
				} else if (arg.equals("-Mr")) {
					maxNumReads = parseIntOption (args, i++, 1, "invalid maximum number of reads");
				} else if (arg.equals("-mr1")) {
					minNumReadsArray1 = parseIntOption (args, i++, 1, "invalid minimum number of reads on arrays of type array1");
				} else if (arg.equals("-Mr1")) {
					maxNumReadsArray1 = parseIntOption (args, i++, 1, "invalid maximum number of reads on arrays of type array1");
				} else if (arg.equals("-mr2")) {
					minNumReadsArray2 = parseIntOption (args, i++, 1, "invalid minimum number of reads on arrays of type array2");
				} else if (arg.equals("-Mr2")) {
					maxNumReadsArray2 = parseIntOption (args, i++, 1, "invalid maximum number of reads on arrays of type array2");
				} else if (arg.equals("-mw")) {
					minNumWrites = parseIntOption (args, i++, 0, "invalid minimum number of writes");
				} else if (arg.equals("-Mw")) {
					maxNumWrites = parseIntOption (args, i++, 0, "invalid maximum number of writes");
				} else if (arg.equals("-mw1")) {
					minNumWritesArray1 = parseIntOption (args, i++, 0, "invalid minimum number of writes on arrays of type array1");
				} else if (arg.equals("-Mw1")) {
					maxNumWritesArray1 = parseIntOption (args, i++, 0, "invalid maximum number of writes on arrays of type array1");
				} else if (arg.equals("-mw2")) {
					minNumWritesArray2 = parseIntOption (args, i++, 0, "invalid minimum number of writes on arrays of type array2");
				} else if (arg.equals("-Mw2")) {
					maxNumWritesArray2 = parseIntOption (args, i++, 0, "invalid maximum number of writes on arrays of type array2");
				} else if (arg.equals("-mxn")) {
					minNumExtBool = parseIntOption (args, i++, 0, "invalid minimum number of array equalities");
				} else if (arg.equals("-Mxn")) {
					maxNumExtBool = parseIntOption (args, i++, 0, "invalid maximum number of array equalities");
				} else if (arg.equals("-mbw")) {
					minBW = parseIntOption (args, i++, 1, "invalid minimum bit-width");
				} else if (arg.equals("-Mbw")) {
					maxBW = parseIntOption (args, i++, 1, "invalid maximum bit-width");      
				} else if(arg.equals("-FPmode")){
					parseIntOption(args, i++, 1, "invalid float mode");
				}
				// TODO: (main) parse command line arguments for FP settings
				
				else { 
					printErrAndExit ("invalid option: " + arg);
				}
			} else {
				printHelpAndExit();
			}
		}

		if (r == null) /* seed has not been set */
			r = new Random();

		assert (numVars >= 0);
		assert (numConsts >= 0);
		assert (minRefs >= 1);

    // TODO: (main) Add FP case for setting parameters and verifying they are in range
    assert(FPMode > 0 && FPMode < 16);
    assert (minArgs > 0);
    assert (maxArgs > 0);
    assert(minNumVarsFloat > 0);
    assert(maxNumVarsFloat > 0);
    assert (minNumUFuncsFloat >= 0);
    assert (maxNumUFuncsFloat >= 0);
    assert (minNumUPredsFloat >= 0);
    assert (maxNumUPredsFloat >= 0);
    assert (minNumConstsFloat >= 0);
    assert (maxNumConstsFloat >= 0);
    
    checkMinMax(minNumVarsFloat, maxNumVarsFloat, "float variables");
    checkMinMax(minNumConstsFloat, maxNumConstsFloat, "float constants");
    checkMinMax(minNumUFuncsFloat, maxNumUFuncsFloat, "uninterpreted float functions");
    checkMinMax(minNumUPredsFloat, maxNumUPredsFloat, "uninterpreted float predicates");
    
    numVarsFloat = selectRandValRange(r, minNumVarsFloat, maxNumVarsFloat);
    numConstsFloat = selectRandValRange(r, minNumConstsFloat, maxNumConstsFloat);
    numUFuncsFloat = selectRandValRange(r, minNumUFuncsFloat, maxNumUFuncsFloat);
    numUPredsFloat = selectRandValRange(r, minNumUPredsFloat, maxNumUPredsFloat);


		boolNodes = new ArrayList<SMTNode>();
		assert (r != null);
		assert (logic != null);
		System.out.println ("(benchmark fuzzsmt");
		System.out.println (":logic " + logic.toString());
		System.out.println (":status unknown");

    // TODO: (main) Add FP case for generating first three layers
    ArrayList<SMTNode> fpNodes = new ArrayList<SMTNode>();
    ArrayList<UFunc> fpuFuncs = new ArrayList<UFunc>();
    ArrayList<UPred> fpuPreds = new ArrayList<UPred>();

    generateUFuncsFP(r, fpuFuncs, numUFuncsFloat, minArgs, maxArgs, FPMode);
    generateUPredsFP(r, fpuPreds, numUPredsFloat, minArgs, maxArgs, FPMode);

    pars += generateFPVars(r, fpNodes, numVarsFloat, FPMode);
    System.out.println(":formula");
    pars += generateFPConsts(r, fpNodes, numConstsFloat, FPMode);
    pars += generateFPLayer(r, fpNodes, FPRM, null);
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
			pars += generateBooleanCNF (r, boolNodes, factor);
			break;
		}
		assert (boolNodes.size() == 1);
		assert (boolNodes.get(0).getType() == BoolType.boolType);
		System.out.println (boolNodes.get(0).getName());

		builder = new StringBuilder (pars);
		for (int i = 0; i < pars; i++)
			builder.append (")");
		builder.append ("\n");
		System.out.println(builder.toString());
		System.exit (0);
	}
}
