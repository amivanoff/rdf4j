/******************************************************************************* 
 * Copyright (c) 2021 Eclipse RDF4J contributors. 
 * All rights reserved. This program and the accompanying materials 
 * are made available under the terms of the Eclipse Distribution License v1.0 
 * which accompanies this distribution, and is available at 
 * http://www.eclipse.org/org/documents/edl-v10.php. 
 *******************************************************************************/
package org.eclipse.rdf4j.model.util;

import static org.eclipse.rdf4j.model.util.Values.bnode;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import org.eclipse.rdf4j.model.BNode;
import org.eclipse.rdf4j.model.IRI;
import org.eclipse.rdf4j.model.Model;
import org.eclipse.rdf4j.model.Resource;
import org.eclipse.rdf4j.model.Statement;
import org.eclipse.rdf4j.model.Value;
import org.eclipse.rdf4j.model.ValueFactory;
import org.eclipse.rdf4j.model.impl.LinkedHashModel;
import org.eclipse.rdf4j.model.impl.SimpleValueFactory;

import com.google.common.base.Charsets;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import com.google.common.collect.Multimaps;
import com.google.common.hash.HashCode;
import com.google.common.hash.HashFunction;
import com.google.common.hash.Hashing;

/**
 * @author jeen
 *
 */
public class GraphComparisons {

	private static final HashFunction hashFunction = Hashing.murmur3_128();

	private static final HashCode initialHashCode = hashFunction.hashString("", Charsets.UTF_8);
	private static final HashCode outgoing = hashFunction.hashString("+", Charsets.UTF_8);
	private static final HashCode incoming = hashFunction.hashString("-", Charsets.UTF_8);
	private static final HashCode distinguisher = hashFunction.hashString("@", Charsets.UTF_8);

	public static boolean isomorphic(Model m1, Model m2) {
		Model c1 = isoCanonicalize(m1);
		Model c2 = isoCanonicalize(m2);
		return (c1.equals(c2));
	}

	public static Model isoCanonicalize(Model m) {
		Map<BNode, HashCode> blankNodeMapping = hashBNodes(m);
		List<Collection<BNode>> partition = partition(blankNodeMapping);

		if (isFine(partition)) {
			return labelModel(m, blankNodeMapping);
		}

		return distinguish(m, blankNodeMapping, partition, null);
	}

	private static Model distinguish(Model m, Map<BNode, HashCode> blankNodeMapping,
			List<Collection<BNode>> partition,
			Model lowestFound) {

		Collections.sort(partition, new Comparator<Collection<BNode>>() {
			public int compare(Collection<BNode> a, Collection<BNode> b) {
				int result = a.size() - b.size();
				if (result == 0) {
					// break tie by comparing value hash
					HashCode hashOfA = blankNodeMapping.get(a.iterator().next());
					HashCode hashOfB = blankNodeMapping.get(b.iterator().next());
					BigInteger difference = new BigInteger(1, hashOfA.asBytes())
							.subtract(new BigInteger(1, hashOfB.asBytes()));
					result = difference.compareTo(BigInteger.ZERO);
				}
				return result;
			}
		});

		Collection<BNode> lowestNonTrivial = partition.stream()
				.filter(part -> part.size() > 1)
				.findFirst()
				.orElseThrow();

		for (BNode node : lowestNonTrivial) {
			HashMap<BNode, HashCode> clonedHash = new HashMap<>(blankNodeMapping);
			clonedHash.put(node, hashTuple(clonedHash.get(node), distinguisher));
			Map<BNode, HashCode> hashDoublePrime = hashBNodes(m, clonedHash);
			List<Collection<BNode>> partitionPrime = partition(hashDoublePrime);
			if (isFine(partitionPrime)) {
				Model gc = labelModel(m, hashDoublePrime);
				if (lowestFound == null || mappingSize(hashDoublePrime).compareTo(mappingSize(blankNodeMapping)) < 0) {
					lowestFound = gc;
				}
			} else {
				lowestFound = distinguish(m, hashDoublePrime, partitionPrime, lowestFound);
			}
		}

		return lowestFound;
	}

	protected static List<Collection<BNode>> partition(Map<BNode, HashCode> blankNodeMapping) {
		List<Collection<BNode>> partition = new ArrayList<>();

		Multimap<HashCode, BNode> invertedMapping = Multimaps.invertFrom(Multimaps.forMap(blankNodeMapping),
				HashMultimap.create());

		for (Entry<HashCode, Collection<BNode>> entry : invertedMapping.asMap().entrySet()) {
			partition.add(entry.getValue());
		}
		return partition;
	}

	private static BigInteger mappingSize(Map<BNode, HashCode> mapping) {
		return mapping.values()
				.stream()
				.map(hashCode -> new BigInteger(1, hashCode.asBytes()))
				.reduce(BigInteger.ZERO, (v1, v2) -> v1.add(v2));
	}

	private static Model labelModel(Model original, Map<BNode, HashCode> hash) {
		Model result = new LinkedHashModel(original.size());

		for (Statement st : original) {
			if (st.getSubject() instanceof BNode || st.getObject() instanceof BNode) {
				Resource subject = st.getSubject() instanceof BNode
						? createCanonicalBNode((BNode) st.getSubject(), hash)
						: st.getSubject();
				IRI predicate = st.getPredicate();
				Value object = st.getObject() instanceof BNode
						? createCanonicalBNode((BNode) st.getObject(), hash)
						: st.getObject();

				result.add(subject, predicate, object);
			} else {
				result.add(st);
			}
		}
		return result;
	}

	protected static Map<BNode, HashCode> hashBNodes(Model m) {
		return hashBNodes(m, null);
	}

	private static Map<BNode, HashCode> hashBNodes(Model m, Map<BNode, HashCode> initialBlankNodeMapping) {
		Map<BNode, HashCode> initialHash = initialBlankNodeMapping == null ? new HashMap<>()
				: new HashMap<>(initialBlankNodeMapping);

		final Set<BNode> blankNodes = new HashSet<>();

		m.subjects().forEach(s -> {
			if (s instanceof BNode) {
				if (!initialHash.containsKey(s)) {
					initialHash.put((BNode) s, initialHashCode);
				}
				blankNodes.add((BNode) s);
			}
		});
		m.objects().forEach(o -> {
			if (o instanceof BNode) {
				if (!initialHash.containsKey(o)) {
					initialHash.put((BNode) o, initialHashCode);
				}
				blankNodes.add((BNode) o);
			}
		});

		Map<BNode, HashCode> currentHash = null;
		if (blankNodes.isEmpty()) {
			currentHash = initialHash;
		} else {
			Map<BNode, HashCode> previousHash = initialHash;
			do {
				Map<BNode, HashCode> temp = currentHash;
				currentHash = new HashMap<>(previousHash);
				previousHash = temp != null ? temp : initialHash;

				for (BNode b : blankNodes) {
					for (Statement st : m.getStatements(b, null, null)) {
						HashCode c = hashTuple(hashForValue(st.getObject(), previousHash),
								hashForValue(st.getPredicate(), previousHash), outgoing);
						currentHash.put(b, hashBag(c, currentHash.get(b)));
					}
					for (Statement st : m.getStatements(null, null, b)) {
						HashCode c = hashTuple(hashForValue(st.getSubject(), previousHash),
								hashForValue(st.getPredicate(), previousHash),
								incoming);
						currentHash.put(b, hashBag(c, currentHash.get(b)));
					}
				}
			} while (!conditionsMet(currentHash, previousHash));
		}
		return currentHash;
	}

	private static HashCode hashTuple(HashCode... hashCodes) {
		return Hashing.combineOrdered(Arrays.asList(hashCodes));
	}

	private static HashCode hashBag(HashCode... hashCodes) {
		return Hashing.combineUnordered(Arrays.asList(hashCodes));
	}

	private static HashCode hashForValue(Value v, Map<BNode, HashCode> mapping) {
		if (v instanceof BNode) {
			return mapping.get(v);
		}
		// TODO optimize by caching hashes
		return hashFunction.hashString(v.stringValue(), Charsets.UTF_8);
	}

	private static BNode createCanonicalBNode(BNode node, Map<BNode, HashCode> mapping) {
		return bnode("iso-" + mapping.get(node).toString());
	}

	private static boolean isFine(List<Collection<BNode>> partition) {
		return partition.stream().allMatch(member -> member.size() == 1);
	}

	private static boolean conditionsMet(Map<BNode, HashCode> currentHash, Map<BNode, HashCode> previousHash) {
		if (currentHash == null || previousHash == null) {
			return false;
		}

		if (!currentHashChanged(currentHash, previousHash)) {
			return true;
		}
		return !containsSharedHashes(currentHash);
	}

	private static boolean currentHashChanged(Map<BNode, HashCode> currentHash, Map<BNode, HashCode> previousHash) {
		for (BNode x : currentHash.keySet()) {
			for (BNode y : currentHash.keySet()) {
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

	private static boolean containsSharedHashes(Map<BNode, HashCode> currentHash) {
		for (BNode x : currentHash.keySet()) {
			for (BNode y : currentHash.keySet()) {
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
