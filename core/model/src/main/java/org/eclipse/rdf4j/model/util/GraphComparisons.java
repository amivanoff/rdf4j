/******************************************************************************* 
 * Copyright (c) 2021 Eclipse RDF4J contributors. 
 * All rights reserved. This program and the accompanying materials 
 * are made available under the terms of the Eclipse Distribution License v1.0 
 * which accompanies this distribution, and is available at 
 * http://www.eclipse.org/org/documents/edl-v10.php. 
 *******************************************************************************/
package org.eclipse.rdf4j.model.util;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

import org.eclipse.rdf4j.model.BNode;
import org.eclipse.rdf4j.model.Model;
import org.eclipse.rdf4j.model.Statement;
import org.eclipse.rdf4j.model.Value;

/**
 * @author jeen
 *
 */
public class GraphComparisons {

	static Map<Value, Integer> createCanonicalHashes(Model m) {
		Map<Value, Integer> initialHash = new HashMap<>();

		List<BNode> subjectBNodes = new ArrayList<>();
		List<BNode> objectBNodes = new ArrayList<>();
		m.subjects().forEach(s -> {
			if (s instanceof BNode) {
				initialHash.put(s, 0);
				subjectBNodes.add((BNode) s);
			} else {
				initialHash.put(s, s.hashCode());
			}
		});
		m.predicates().forEach(p -> initialHash.put(p, p.hashCode()));
		m.objects().forEach(o -> {
			if (o instanceof BNode) {
				initialHash.put(o, 0);
				objectBNodes.add((BNode) o);
			} else {
				initialHash.put(o, o.hashCode());
			}
		});

		Map<Value, Integer> previousHash = initialHash;
		Map<Value, Integer> currentHash = null;
		do {
			Map<Value, Integer> temp = currentHash;
			currentHash = new HashMap<>(previousHash);
			previousHash = temp != null ? temp : initialHash;

			for (BNode b : subjectBNodes) {
				for (Statement st : m.getStatements(b, null, null)) {
					int c = hashTuple(previousHash.get(st.getObject()), previousHash.get(st.getPredicate()), "+");
					currentHash.put(b, hashBag(c, currentHash.get(b)));
				}
			}
		} while (!conditionsMet(currentHash, previousHash));

		return currentHash;
	}

	/**
	 * @param c
	 * @param integer
	 * @return
	 */
	private static Integer hashBag(int c, Integer integer) {
		return Objects.hash(c, integer);
	}

	/**
	 * @param integer
	 * @param integer2
	 * @param string
	 * @return
	 */
	private static int hashTuple(Integer integer, Integer integer2, String string) {
		return Objects.hash(integer, integer2, string);
	}

	private static boolean conditionsMet(Map<Value, Integer> currentHash, Map<Value, Integer> previousHash) {
		if (currentHash == null || previousHash == null) {
			return false;
		}

		if (!currentHashChanged(currentHash, previousHash)) {
			return true;
		}
		return !containsSharedHashes(currentHash);
	}

	private static boolean currentHashChanged(Map<Value, Integer> currentHash, Map<Value, Integer> previousHash) {
		for (Value x : currentHash.keySet()) {
			for (Value y : currentHash.keySet()) {
				if (currentHash.get(x).equals(currentHash.get(y))) {
					if (!previousHash.get(x).equals(previousHash.get(y))) {
						return true;
					}
				} else if (previousHash.get(x).equals(previousHash.get(y))) {
					return true;
				}
			}
		}

		return false;
	}

	private static boolean containsSharedHashes(Map<Value, Integer> currentHash) {
		for (Value x : currentHash.keySet()) {
			for (Value y : currentHash.keySet()) {
				if (x.equals(y)) {
					if (!currentHash.get(x).equals(currentHash.get(y))) {
						return true;
					}
				} else if (currentHash.get(x).equals(currentHash.get(y))) {
					return true;
				}
			}
		}
		return false;
	}
}
