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
import java.util.stream.Collectors;

import org.eclipse.rdf4j.model.BNode;
import org.eclipse.rdf4j.model.IRI;
import org.eclipse.rdf4j.model.Model;
import org.eclipse.rdf4j.model.Resource;
import org.eclipse.rdf4j.model.Statement;
import org.eclipse.rdf4j.model.Value;
import org.eclipse.rdf4j.model.impl.LinkedHashModel;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

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

	private static final Logger logger = LoggerFactory.getLogger(GraphComparisons.class);

	private static final HashFunction hashFunction = Hashing.murmur3_128();

	private static final HashCode initialHashCode = hashFunction.hashString("", Charsets.UTF_8);
	private static final HashCode outgoing = hashFunction.hashString("+", Charsets.UTF_8);
	private static final HashCode incoming = hashFunction.hashString("-", Charsets.UTF_8);
	private static final HashCode distinguisher = hashFunction.hashString("@", Charsets.UTF_8);

	public static boolean isomorphic(Model m1, Model m2) {
		if (m1.size() != m2.size()) {
			return false;
		}

		final Model c1 = isoCanonicalize(m1);
		final Model c2 = isoCanonicalize(m2);
		return (c1.equals(c2));
	}

	public static Model isoCanonicalize(Model m) {
		Map<BNode, HashCode> blankNodeMapping = hashBNodes(m);
		Multimap<HashCode, BNode> partition = partitionMapping(blankNodeMapping);

		if (isFine(partition)) {
			return labelModel(m, blankNodeMapping);
		}

		return distinguish(m, blankNodeMapping, partition, null, new ArrayList<>(), new ArrayList<>());
	}

	static Set<BNode> getBlankNodes(Model m) {
		final Set<BNode> blankNodes = new HashSet<>();

		m.subjects().forEach(s -> {
			if (s instanceof BNode) {
				blankNodes.add((BNode) s);
			}
		});
		m.objects().forEach(o -> {
			if (o instanceof BNode) {
				blankNodes.add((BNode) o);
			}
		});

		return blankNodes;
	}

	private static Model distinguish(Model m, Map<BNode, HashCode> blankNodeMapping,
			Multimap<HashCode, BNode> partitionMapping,
			Model lowestFound, List<BNode> parentFixpoints, List<Map<BNode, HashCode>> finePartitionMappings) {

		final List<Collection<BNode>> sortedPartitions = new ArrayList<>(partitionMapping.asMap().values());
		Collections.sort(sortedPartitions, new Comparator<Collection<BNode>>() {
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

		Collection<BNode> lowestNonTrivialPartition = sortedPartitions.stream()
				.filter(part -> part.size() > 1)
				.findFirst()
				.orElseThrow();

		for (BNode node : lowestNonTrivialPartition) {
			List<BNode> fixpoints = new ArrayList<>(parentFixpoints);
			fixpoints.add(node);
			HashMap<BNode, HashCode> clonedHash = new HashMap<>(blankNodeMapping);
			clonedHash.put(node, hashTuple(clonedHash.get(node), distinguisher));
			Map<BNode, HashCode> hashDoublePrime = hashBNodes(m, clonedHash);

			Multimap<HashCode, BNode> partitionPrime = partitionMapping(hashDoublePrime);
			if (isFine(partitionPrime)) {
				finePartitionMappings.add(hashDoublePrime);
				if (lowestFound == null || mappingSize(hashDoublePrime).compareTo(mappingSize(blankNodeMapping)) < 0) {
					lowestFound = labelModel(m, hashDoublePrime);
				}
			} else {
				Map<BNode, BNode> compatibleAutomorphism = findCompatibleAutomorphism(fixpoints, finePartitionMappings);
				if (compatibleAutomorphism != null) {
					// prune
					continue;
				}
				lowestFound = distinguish(m, hashDoublePrime, partitionPrime, lowestFound, fixpoints,
						finePartitionMappings);
			}
		}

		return lowestFound;
	}

	static Map<BNode, BNode> findCompatibleAutomorphism(List<BNode> fixpoints,
			List<Map<BNode, HashCode>> partitionMappings) {
		// check if two mappings with identical hash codes exist
		for (Map<BNode, HashCode> mapping : partitionMappings) {
			Map<BNode, HashCode> compatibleMapping = null;
			for (Map<BNode, HashCode> om : partitionMappings) {
				if (om.equals(mapping)) {
					continue;
				}

				List<HashCode> difference = new ArrayList<>(om.values());
				difference.removeAll(mapping.values());
				if (difference.isEmpty()) {
					compatibleMapping = om;
					break;
				}
			}

			if (compatibleMapping != null) {
				Map<HashCode, BNode> invertedMapping = mapping.entrySet()
						.stream()
						.collect(Collectors.toMap(Entry::getValue, Entry::getKey));

				Map<BNode, BNode> automorphism = new HashMap<>();
				for (Entry<BNode, HashCode> entry : compatibleMapping.entrySet()) {
					automorphism.put(entry.getKey(), invertedMapping.get(entry.getValue()));
				}
				// check if fixpoints all map, if so we have a compatible automorphism
				for (BNode fixpoint : fixpoints) {
					if (!automorphism.get(fixpoint).equals(fixpoint)) {
						break;
					}
					return automorphism;
				}
			}
		}
		return null;
	}

	protected static List<Collection<BNode>> partitions(Multimap<HashCode, BNode> partitionMapping) {
		List<Collection<BNode>> partition = new ArrayList<>();

		for (Entry<HashCode, Collection<BNode>> entry : partitionMapping.asMap().entrySet()) {
			partition.add(entry.getValue());
		}
		return partition;
	}

	protected static Multimap<HashCode, BNode> partitionMapping(Map<BNode, HashCode> blankNodeMapping) {
		return Multimaps.invertFrom(Multimaps.forMap(blankNodeMapping), HashMultimap.create());
	}

	private static BigInteger mappingSize(Map<BNode, HashCode> mapping) {
		BigInteger size = mapping.values()
				.stream()
				.map(hashCode -> new BigInteger(1, hashCode.asBytes()))
				.reduce(BigInteger.ZERO, (v1, v2) -> v1.add(v2));
		return size;
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
		final Map<BNode, HashCode> initialHash = initialBlankNodeMapping == null ? new HashMap<>()
				: new HashMap<>(initialBlankNodeMapping);
		final Map<Value, HashCode> staticValueMapping = new HashMap<>();

		final Set<BNode> blankNodes = getBlankNodes(m);
		if (initialHash.isEmpty()) {
			blankNodes.forEach(node -> initialHash.put(node, initialHashCode));
		}

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
						HashCode c = hashTuple(hashForValue(st.getObject(), previousHash, staticValueMapping),
								hashForValue(st.getPredicate(), previousHash, staticValueMapping), outgoing);
						currentHash.put(b, hashBag(c, currentHash.get(b)));
					}
					for (Statement st : m.getStatements(null, null, b)) {
						HashCode c = hashTuple(hashForValue(st.getSubject(), previousHash, staticValueMapping),
								hashForValue(st.getPredicate(), previousHash, staticValueMapping),
								incoming);
						currentHash.put(b, hashBag(c, currentHash.get(b)));
					}
				}
			} while (!fullyDistinguished(currentHash, previousHash));
		}
		return currentHash;
	}

	protected static HashCode hashTuple(HashCode... hashCodes) {
		return Hashing.combineOrdered(Arrays.asList(hashCodes));
	}

	protected static HashCode hashBag(HashCode... hashCodes) {
		return Hashing.combineUnordered(Arrays.asList(hashCodes));
	}

	private static HashCode hashForValue(Value value, Map<BNode, HashCode> bnodeMapping,
			Map<Value, HashCode> staticValueMapping) {
		if (value instanceof BNode) {
			return bnodeMapping.get(value);
		}
		return staticValueMapping.computeIfAbsent(value,
				v -> hashFunction.hashString(v.stringValue(), Charsets.UTF_8));
	}

	private static BNode createCanonicalBNode(BNode node, Map<BNode, HashCode> mapping) {
		return bnode("iso-" + mapping.get(node).toString());
	}

	private static boolean isFine(Multimap<HashCode, BNode> partitionMapping) {
		return partitionMapping.asMap().values().stream().allMatch(member -> member.size() == 1);
	}

	private static boolean fullyDistinguished(Map<BNode, HashCode> currentHash, Map<BNode, HashCode> previousHash) {
		if (currentHash == null || previousHash == null) {
			return false;
		}

		final Multimap<HashCode, BNode> currentPartitionMapping = partitionMapping(currentHash);
		if (isFine(currentPartitionMapping)) { // no two terms share a hash
			return true;
		}

		return currentUnchanged(currentPartitionMapping, previousHash);
	}

	private static boolean currentUnchanged(Multimap<HashCode, BNode> current, Map<BNode, HashCode> previousHash) {
		// current is unchanged if: all bnodes that have the same hashcode in current also shared the same hashcode in
		// previous, and all bnodes that have different ones in current also have different ones in previous.

		final Multimap<HashCode, BNode> previous = partitionMapping(previousHash);
		for (Collection<BNode> currentSharedHashNodes : current.asMap().values()) {
			// pick a BNode, doesn't matter which: they all share the same hashcode
			BNode node = currentSharedHashNodes.iterator().next();

			HashCode previousHashCode = previousHash.get(node);
			if (!previous.get(previousHashCode).equals(currentSharedHashNodes)) {
				return false;
			}
		}
		return true;
	}

}
