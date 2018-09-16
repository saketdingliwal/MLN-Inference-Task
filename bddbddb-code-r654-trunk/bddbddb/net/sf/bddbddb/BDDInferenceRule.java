// Copyright (C) 2004 John Whaley <jwhaley@alum.mit.edu>
// Licensed under the terms of the GNU LGPL; see COPYING for details.
package net.sf.bddbddb;

import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import jwutil.collections.LinearMap;
import jwutil.io.SystemProperties;
import jwutil.util.Assert;
import net.sf.javabdd.BDD;
import net.sf.javabdd.BDDDomain;
import net.sf.javabdd.BDDFactory;
import net.sf.javabdd.BDDPairing;
import net.sf.javabdd.BDDVarSet;

/**
 * An implementation of InferenceRule that uses BDDs.
 * 
 * @author jwhaley
 * @version $Id: BDDInferenceRule.java 650 2006-11-29 08:08:45Z joewhaley $
 */
public class BDDInferenceRule extends InferenceRule {
    /**
     * @see net.sf.bddbddb.InferenceRule#solver
     */
    protected BDDSolver solver;
    
    /**
     * Values for subgoals, used for incrementalization.
     */
    protected BDD[] oldRelationValues;
    
    /**
     * Map from variables to their BDD domains.
     */
    protected Map variableToBDDDomain;
    
    /**
     * Set of renames that must occur after each of the subgoals.
     */
    BDDPairing[] renames;
    
    /**
     * Rename operation that must occur to match with the head relation.
     */
    BDDPairing bottomRename;
    
    /**
     * BDD variables that can be quantified away after each step.
     */
    BDDVarSet[] canQuantifyAfter;
    
    /**
     * Collection of variables that are still active after each step.
     */
    Collection[] variableSet;
    
    /**
     * Number of times update() has been called on this rule.
     */
    public int updateCount;
    
    /**
     * Total time (in ms) spent updating this rule.
     */
    long totalTime;
    int longestIteration = 0;
    long longestTime = 0;

    
    /**
     * Whether we should attempt to find the best order for this rule.
     */
    boolean find_best_order = !SystemProperties.getProperty("findbestorder", "no").equals("no");
    
    long FBO_CUTOFF = Long.parseLong(SystemProperties.getProperty("fbocutoff", "90"));
    
    long DUMP_CUTOFF = Long.parseLong(SystemProperties.getProperty("dumpcutoff", "5000"));
    
    /**
     * Construct a new BDDInferenceRule.
     * Only to be called internally.
     * 
     * @param solver
     * @param top
     * @param bottom
     */
    BDDInferenceRule(BDDSolver solver, List/*<RuleTerm>*/ top, RuleTerm bottom) {
        super(solver, top, bottom);
        this.solver = solver;
        updateCount = 0;
        //initialize();
    }

    /*
     * (non-Javadoc)
     * 
     * @see net.sf.bddbddb.InferenceRule#copyOptions(net.sf.bddbddb.InferenceRule)
     */
    public void copyOptions(InferenceRule r) {
        super.copyOptions(r);
        if (r instanceof BDDInferenceRule) {
            BDDInferenceRule that = (BDDInferenceRule) r;
            this.find_best_order = that.find_best_order;
        }
    }

    /*
     * (non-Javadoc)
     * 
     * @see net.sf.bddbddb.InferenceRule#initialize()
     */
    void initialize() {
        if (isInitialized) return;
        super.initialize();
        if (TRACE) solver.out.println("Initializing BDDInferenceRule " + this);
        updateCount = 0;
        this.oldRelationValues = null;
        this.variableToBDDDomain = new HashMap();
        for (int i = 0; i < top.size(); ++i) {
            RuleTerm rt = (RuleTerm) top.get(i);
            BDDRelation r = (BDDRelation) rt.relation;
            for (int j = 0; j < rt.variables.size(); ++j) {
                Variable v = (Variable) rt.variables.get(j);
                // In the relation, this variable uses domain d
                BDDDomain d = (BDDDomain) r.domains.get(j);
                Assert._assert(d != null);
                // In the rule, we use domain d2
                BDDDomain d2 = (BDDDomain) variableToBDDDomain.get(v);
                if (d2 == null) {
                    if (!variableToBDDDomain.containsValue(d)) {
                        d2 = d;
                    } else {
                        // need to use a new BDDDomain
                        Attribute a = (Attribute) r.attributes.get(j);
                        Domain fd = a.attributeDomain;
                        Collection existingBDDDomains = solver.getBDDDomains(fd);
                        for (Iterator k = existingBDDDomains.iterator(); k.hasNext();) {
                            BDDDomain d3 = (BDDDomain) k.next();
                            if (!variableToBDDDomain.containsValue(d3)) {
                                d2 = d3;
                                break;
                            }
                        }
                        if (d2 == null) {
                            d2 = solver.allocateBDDDomain(fd);
                        }
                    }
                    if (TRACE) solver.out.println("Variable " + v + " allocated to BDD domain " + d2);
                    variableToBDDDomain.put(v, d2);
                } else {
                    //if (TRACE) solver.out.println("Variable "+v+" already
                    // allocated to BDD domain "+d2);
                }
            }
        }
        if (this.renames == null) {
            renames = new BDDPairing[top.size()];
        }
        for (int i = 0; i < top.size(); ++i) {
            RuleTerm rt = (RuleTerm) top.get(i);
            // Don't reset, because it is shared across rules.
            //if (renames[i] != null) renames[i].reset();
            renames[i] = calculateRenames(rt, true);
        }
        // Don't reset, because it is shared across rules.
        //if (bottomRename != null) bottomRename.reset();
        bottomRename = calculateRenames(bottom, false);
        initializeQuantifySet();
        if (variableSet == null) {
            variableSet = new Collection[top.size()];
        }
        Collection currentVariableSet = new LinkedList();
        for (int i = 0; i < top.size(); ++i) {
            RuleTerm rt = (RuleTerm) top.get(i);
            currentVariableSet.addAll(rt.variables);
            if (TRACE) solver.out.println("Calculating quantifiable variables for "+rt);
            outer : for (Iterator k = rt.variables.iterator(); k.hasNext();) {
                Variable v = (Variable) k.next();
                if (bottom.variables.contains(v)) continue;
                for (int j = i + 1; j < top.size(); ++j) {
                    RuleTerm rt2 = (RuleTerm) top.get(j);
                    if (rt2.variables.contains(v)) continue outer;
                }
                if (TRACE) solver.out.println("Can quantify "+v);
                currentVariableSet.remove(v);
            }
            variableSet[i] = currentVariableSet;
            if (TRACE) solver.out.println("Variable set["+i+"]="+variableSet[i]);
            currentVariableSet = new LinkedList(currentVariableSet);
        }
        isInitialized = true;
    }

    /**
     * Initialize the oldRelationValues to be the zero BDD.
     */
    private void initializeOldRelationValues() {
        this.oldRelationValues = new BDD[top.size()];
        for (int i = 0; i < oldRelationValues.length; ++i) {
            oldRelationValues[i] = solver.bdd.zero();
        }
    }

    void initializeQuantifySet() {
        if (canQuantifyAfter == null) {
            canQuantifyAfter = new BDDVarSet[top.size()];
        }
        for (int i = 0; i < top.size(); ++i) {
            RuleTerm rt = (RuleTerm) top.get(i);
            if (canQuantifyAfter[i] != null) canQuantifyAfter[i].free();
            canQuantifyAfter[i] = solver.bdd.emptySet();
            outer : for (Iterator k = rt.variables.iterator(); k.hasNext();) {
                Variable v = (Variable) k.next();
                if (bottom.variables.contains(v)) continue;
                for (int j = i + 1; j < top.size(); ++j) {
                    RuleTerm rt2 = (RuleTerm) top.get(j);
                    if (rt2.variables.contains(v)) continue outer;
                }
                BDDDomain d2 = (BDDDomain) variableToBDDDomain.get(v);
                canQuantifyAfter[i].unionWith(d2.set());
            }
        }
    }
    
    /**
     * Calculate the rename operations that are needed for the given term.
     * The direction flag determines the desired direction of the renames.
     * If direction is true, we rename from the BDDDomain specified by the
     * relation to the BDDDomain used by the rule for that variable.
     * If direction is false, we rename from the BDDDomain used by the rule
     * to the BDDDomain used by the relation.
     * 
     * @param rt  term to calculate renames for
     * @param direction  direction of desired renames
     * @return  BDDPairing that contains the renames
     */
    private BDDPairing calculateRenames(RuleTerm rt, boolean direction) {
        BDDRelation r = (BDDRelation) rt.relation;
        if (TRACE) solver.out.println("Calculating renames for " + r);
        Map pairing = null;
        for (int j = 0; j < rt.variables.size(); ++j) {
            Variable v = (Variable) rt.variables.get(j);
            if (unnecessaryVariables.contains(v)) continue;
            BDDDomain d = (BDDDomain) r.domains.get(j);
            BDDDomain d2 = (BDDDomain) variableToBDDDomain.get(v);
            Assert._assert(d2 != null);
            if (d != d2) {
                if (!direction) {
                    BDDDomain d3 = d2;
                    d2 = d;
                    d = d3;
                }
                if (TRACE) solver.out.println(rt + " variable " + v + ": replacing " + d + " -> " + d2);
                if (pairing == null) pairing = new LinearMap(solver.bdd.numberOfDomains());
                Object foo = pairing.put(d, d2);
                Assert._assert(foo == null);
            }
        }
        return pairing != null ? solver.getPairing(pairing) : null;
    }

    void doPreUpdate(BDD oldValue) {
        if (preCode != null) {
            for (Iterator i = preCode.iterator(); i.hasNext(); ) {
                CodeFragment f = (CodeFragment) i.next();
                f.invoke(this, oldValue);
            }
        }
    }
    
    void doPostUpdate(BDD oldValue) {
        if (postCode != null) {
            for (Iterator i = postCode.iterator(); i.hasNext(); ) {
                CodeFragment f = (CodeFragment) i.next();
                f.invoke(this, oldValue);
            }
        }
    }
    
    /*
     * (non-Javadoc)
     * 
     * @see net.sf.bddbddb.InferenceRule#update()
     */
    public boolean update() {
        doPreUpdate(((BDDRelation) bottom.relation).relation);
        ++updateCount;
        if (incrementalize) {
            if (oldRelationValues != null) return updateIncremental();
        }
        // non-incremental version.
        if (solver.NOISY) solver.out.println("Applying inference rule:\n   " + this + " (" + updateCount + ")");
        long time = 0L;
        long ttime = 0L;
        if (solver.REPORT_STATS || TRACE) time = System.currentTimeMillis();
        BDD[] relationValues = new BDD[top.size()];
        
        // Quantify out unnecessary fields in input relations.
        if (!quantifyAndRestrict(relationValues)) {
            if (solver.REPORT_STATS) totalTime += System.currentTimeMillis() - time;
            if (TRACE) solver.out.println("Time spent: " + (System.currentTimeMillis() - time));
            doPostUpdate(null);
            return false;
        }
        
        // Handling universal quantification.
        if (!handleUniversalQuantification(relationValues)) {
            if (solver.REPORT_STATS) totalTime += System.currentTimeMillis() - time;
            if (TRACE) solver.out.println("Time spent: " + (System.currentTimeMillis() - time));
            doPostUpdate(null);
            return false;
        }
        
        // If we are incrementalizing, cache copies of the input relations.
        // This happens after we have quantified away and restricted constants,
        // but before we do renaming.
        if (incrementalize && cache_before_rename) {
            if (TRACE) {
                solver.out.print("Caching values of input relations");
                ttime = System.currentTimeMillis();
            }
            if (oldRelationValues == null) initializeOldRelationValues();
            for (int i = 0; i < relationValues.length; ++i) {
                oldRelationValues[i].orWith(relationValues[i].id());
            }
            if (TRACE) solver.out.println(" (" + (System.currentTimeMillis() - ttime) + " ms)");
        }
        // Replace BDDDomain's in the BDD relations to match variable
        // assignments.
        for (int i = 0; i < top.size(); ++i) {
            RuleTerm rt = (RuleTerm) top.get(i);
            BDDRelation r = (BDDRelation) rt.relation;
            if (TRACE) solver.out.println("Relation " + r + " " + relationValues[i].nodeCount() + " nodes, domains " + domainsOf(relationValues[i]));
            if (TRACE_FULL) solver.out.println("   current value: " + relationValues[i].toStringWithDomains());
            BDDPairing pairing = renames[i];
            if (pairing != null) {
                if (TRACE) {
                    solver.out.print("Relation " + r + " domains " + domainsOf(relationValues[i]) + " -> ");
                    ttime = System.currentTimeMillis();
                }
                relationValues[i].replaceWith(pairing);
                if (TRACE) {
                    solver.out.print(domainsOf(relationValues[i]));
                    solver.out.println(" (" + (System.currentTimeMillis() - ttime) + " ms)");
                }
            }
        }
        BDDRelation r = (BDDRelation) bottom.relation;
        if (TRACE_FULL) solver.out.println("Current value of relation " + bottom + ": " + r.relation.toStringWithDomains());
        // If we are incrementalizing, cache copies of the input relations.
        // If the option is set, we do this after the rename.
        if (incrementalize && !cache_before_rename) {
            if (TRACE) {
                solver.out.print("Caching values of input relations");
                ttime = System.currentTimeMillis();
            }
            if (oldRelationValues == null) initializeOldRelationValues();
            for (int i = 0; i < relationValues.length; ++i) {
                oldRelationValues[i].orWith(relationValues[i].id());
            }
            if (TRACE) solver.out.println(" (" + (System.currentTimeMillis() - ttime) + " ms)");
        }
        
        BDD result = evalRelations(solver.bdd, relationValues, canQuantifyAfter, time);
        long thisTime = System.currentTimeMillis() - time;
        if (result == null) {
            doPostUpdate(null);
            return false;
        }
        if (TRACE_FULL) solver.out.println(" = " + result.toStringWithDomains());

        else if (TRACE) solver.out.println(" = " + result.nodeCount());
        if (single) {
            // Limit the result tuples to a single one.
            result = limitToSingle(result);
            if (TRACE) solver.out.println("Limited to single satisfying tuple: " + result.nodeCount());
        }
        if (bottomRename != null) {
            if (TRACE) {
                solver.out.print("Result domains " + domainsOf(result) + " -> ");
                ttime = System.currentTimeMillis();
            }
            result.replaceWith(bottomRename);
            if (TRACE) {
                solver.out.print(domainsOf(result));
                solver.out.println(" (" + (System.currentTimeMillis() - ttime) + " ms)");
            }
        }
        for (int i = 0; i < bottom.variables.size(); ++i) {
            Variable v = (Variable) bottom.variables.get(i);
            if (v instanceof Constant) {
                Constant c = (Constant) v;
                BDDDomain d = (BDDDomain) r.domains.get(i);
                if (TRACE) {
                    solver.out.print("Restricting result domain " + d + " to constant " + c);
                    ttime = System.currentTimeMillis();
                }
                result.andWith(d.ithVar(c.value));
                if (TRACE) {
                    solver.out.println(" (" + (System.currentTimeMillis() - ttime) + " ms)");
                }
            }
        }
        BDD oldRelation = r.relation.id();
        if (TRACE_FULL) solver.out.println("Adding to " + bottom + ": " + result.toStringWithDomains());
        if (TRACE) {
            solver.out.print("Result: " + r.relation.nodeCount() + " nodes -> ");
            ttime = System.currentTimeMillis();
        }
        r.relation.orWith(result);
        if (TRACE) {
            solver.out.print(r.relation.nodeCount() + " nodes, ");
            solver.out.print(r.dsize() + " elements.");
            solver.out.println(" (" + (System.currentTimeMillis() - ttime) + " ms)");
        }
        if (TRACE_FULL) solver.out.println("Relation " + r + " is now: " + r.relation.toStringWithDomains());
        boolean changed = !oldRelation.equals(r.relation);
        if (TRACE) solver.out.println("Relation " + r + " changed: " + changed);
        if (solver.REPORT_STATS) totalTime += System.currentTimeMillis() - time;
        if (TRACE) solver.out.println("Time spent: " + (System.currentTimeMillis() - time));
        r.updateNegated();
        r.doUpdate(oldRelation);
        if (r.negated != null) {
            BDD old_neg = oldRelation.not(); 
            ((BDDRelation)r.negated).doUpdate(old_neg);
            old_neg.free();
        }
        doPostUpdate(oldRelation);
        oldRelation.free();
        return changed;
    }

    public BDD evalRelations(BDDFactory bdd, BDD[] relationValues, BDDVarSet[] canQuantifyAfter, long time) {
        
        long ttime = 0;
        BDD result = bdd.universe();
        for (int j = 0; j < relationValues.length; ++j) {
            RuleTerm rt = (RuleTerm) top.get(j);
            BDDVarSet canNowQuantify = canQuantifyAfter[j];
            if (TRACE) solver.out.print(" x " + rt.relation);
            BDD b = relationValues[j];
            if (TRACE) {
                solver.out.print(" (relprod " + b.nodeCount());
                solver.out.print(" ("+domainsOf(b)+")/");
                solver.out.print("("+domainsOf(canNowQuantify)+")");
            }
            if (TRACE || find_best_order || DUMP_CUTOFF > 0) ttime = System.currentTimeMillis();
            BDD topBdd = result.relprod(b, canNowQuantify);
            if (TRACE || find_best_order || DUMP_CUTOFF > 0) ttime = System.currentTimeMillis() - ttime;
            if (DUMP_CUTOFF > 0 && ttime >= DUMP_CUTOFF &&
                SystemProperties.getPropertyFromFile("dumpslow") != null) {
                long ftime = System.currentTimeMillis();
                // Dump this operation to disk so we can analyze it later.
                try {
                    String baseName = solver.getBaseName()+"rule"+id+"_subgoal"+j+"_update"+updateCount;
                    Writer w = new FileWriter(baseName+".info");
                    w.write("Rule: "+this+"\n");
                    w.write("Time: "+ttime+" ms\n");
                    w.close();
                    BDDRelation.save(solver, baseName+"_op1.bdd", result);
                    BDDRelation.save(solver, baseName+"_op2.bdd", b);
                    BDDRelation.save(solver, baseName+"_op3.bdd", canNowQuantify.toBDD());
                } catch (IOException x) {
                    System.err.println("Error dumping BDD: "+x);
                }
                ftime = System.currentTimeMillis() - ftime;
                this.totalTime -= ftime;
            }
            if (find_best_order && !result.isOne() && ttime >= FBO_CUTOFF) {
                long ftime = System.currentTimeMillis();
                FindBestDomainOrder.findBestDomainOrder(solver,this, j,solver.bdd, result, b, canNowQuantify,
                        (RuleTerm) top.get(j-1), rt,
                        variableSet[j], rt.variables);
                // Correct for learning time.
                ftime = System.currentTimeMillis() - ftime;
                this.totalTime -= ftime;
            }
            b.free();
            if (TRACE) {
                solver.out.print("=" + topBdd.nodeCount());
                solver.out.print(" (" + domainsOf(topBdd) + ")");
                solver.out.print(") (" + ttime + " ms)");
            }
            result.free();
            result = topBdd;
            if (result.isZero()) {
                if (TRACE) solver.out.println(" Became empty, stopping.");
                for (++j; j < relationValues.length; ++j) {
                    relationValues[j].free();
                }
                if (solver.REPORT_STATS) totalTime += System.currentTimeMillis() - time;
                if (TRACE) solver.out.println("Time spent: " + (System.currentTimeMillis() - time));
                return null;
            }
   
        }
        return result;
    }
    
    private boolean handleUniversalQuantification(BDD[] relationValues) {
        if (TRACE) solver.out.println("Handling universal quantification...");
        long ttime = 0L;
        for (int i = 0; i < top.size(); ++i) {
            RuleTerm rt = (RuleTerm) top.get(i);
            BDDRelation r = (BDDRelation) rt.relation;
            //relationValues[i] = r.relation.id();
            for (int j = 0; j < rt.variables.size(); ++j) {
                Variable v = (Variable) rt.variables.get(j);
                BDDDomain d = (BDDDomain) r.domains.get(j);
                if (v instanceof Universe) {
                    if (TRACE) {
                        solver.out.print("Universe: for all " + d);
                        ttime = System.currentTimeMillis();
                    }
                    BDDVarSet dset = d.set();
                    BDD q = relationValues[i].forAll(dset);
                    dset.free();
                    if (TRACE) solver.out.println(" (" + (System.currentTimeMillis() - ttime) + " ms)");
                    relationValues[i].free();
                    relationValues[i] = q;
                    continue;
                }
            }
            if (relationValues[i].isZero()) {
                if (TRACE) solver.out.println("Relation " + r + " is now empty!  Stopping early.");
                for (int j = 0; j <= i; ++j) {
                    relationValues[j].free();
                }
                return false;
            }
        }
        return true;
    }
    
    private boolean quantifyAndRestrict(BDD[] relationValues) {
        long ttime = 0L;
        if (TRACE) solver.out.println("Quantifying out unnecessary domains and restricting constants...");
        if (TRACE) solver.out.println("Variables: necessary=" + necessaryVariables + " unnecessary=" + unnecessaryVariables);
        for (int i = 0; i < top.size(); ++i) {
            RuleTerm rt = (RuleTerm) top.get(i);
            BDDRelation r = (BDDRelation) rt.relation;
            relationValues[i] = r.relation.id();
            for (int j = 0; j < rt.variables.size(); ++j) {
                Variable v = (Variable) rt.variables.get(j);
                BDDDomain d = (BDDDomain) r.domains.get(j);
                if (v instanceof Constant) {
                    if (TRACE) {
                        solver.out.print("Constant: restricting " + r + " " + d + " = " + v);
                        ttime = System.currentTimeMillis();
                    }
                    relationValues[i].restrictWith(d.ithVar(((Constant) v).value));
                    if (TRACE) {
                        solver.out.print(" (" + (System.currentTimeMillis() - ttime) + " ms)");
                        solver.out.println(" (" + relationValues[i].nodeCount() + " nodes)");
                    }
                    continue;
                }
                if (v instanceof Universe) {
                    // Handled later.
                    continue;
                }
                if (unnecessaryVariables.contains(v)) {
                    if (TRACE) {
                        solver.out.print(v + " is unnecessary, quantifying out " + d);
                        ttime = System.currentTimeMillis();
                    }
                    BDDVarSet dset = d.set();
                    BDD q = relationValues[i].exist(dset);
                    dset.free();
                    if (TRACE) {
                        solver.out.print(" (" + (System.currentTimeMillis() - ttime) + " ms)");
                        solver.out.println(" (" + q.nodeCount() + " nodes)");
                    }
                    relationValues[i].free();
                    relationValues[i] = q;
                }
            }
            if (relationValues[i].isZero()) {
                if (TRACE) solver.out.println("Relation " + r + " is now empty!  Stopping early.");
                for (int j = 0; j <= i; ++j)
                    relationValues[j].free();
                return false;
            }
        }
        return true;
    }
    
    /**
     * Incremental version of update().
     * 
     * @return  if the head relation changed
     */
    private boolean updateIncremental() {
        if (solver.NOISY) solver.out.println("Applying inference rule:\n   " + this + " (inc) (" + updateCount + ")");
        long time = 0L;
        long ttime = 0L;
        if (solver.REPORT_STATS || TRACE) time = System.currentTimeMillis();
        BDD[] allRelationValues = new BDD[top.size()];
        BDD[] newRelationValues = new BDD[top.size()];
        
        // Quantify out unnecessary fields in input relations.
        if (!quantifyAndRestrict(allRelationValues)) {
            if (solver.REPORT_STATS) totalTime += System.currentTimeMillis() - time;
            if (TRACE) solver.out.println("Time spent: " + (System.currentTimeMillis() - time));
            doPostUpdate(null);
            return false;
        }
        
        // Handling universal quantification.
        if (!handleUniversalQuantification(allRelationValues)) {
            if (solver.REPORT_STATS) totalTime += System.currentTimeMillis() - time;
            if (TRACE) solver.out.println("Time spent: " + (System.currentTimeMillis() - time));
            doPostUpdate(null);
            return false;
        }
        
        // If we cached before renaming, diff with cache now.
        boolean[] needWholeRelation = null;
        if (cache_before_rename) {
            needWholeRelation = new boolean[allRelationValues.length];
            for (int i = 0; i < allRelationValues.length; ++i) {
                if (!allRelationValues[i].equals(oldRelationValues[i])) {
                    if (TRACE) {
                        Relation r = ((RuleTerm) top.get(i)).relation;
                        solver.out.print("Diff relation #" + i + " ("+r+") : (" + allRelationValues[i].nodeCount() + "x" + oldRelationValues[i].nodeCount()
                            + "=");
                        //solver.out.println(oldRelationValues[i]);
                        ttime = System.currentTimeMillis();
                    }
                    newRelationValues[i] = allRelationValues[i].apply(oldRelationValues[i], BDDFactory.diff);
                    if (TRACE) {
                        solver.out.print(newRelationValues[i].nodeCount() + ")");
                        solver.out.println(" (" + (System.currentTimeMillis() - ttime) + " ms)");
                    }
                    if (TRACE_FULL) {
                        solver.out.println("New for relation #" + i + ": " + newRelationValues[i].toStringWithDomains());
                    }
                    Assert._assert(!newRelationValues[i].isZero());
                    for (int j = 0; j < needWholeRelation.length; ++j) {
                        if (i == j) continue;
                        needWholeRelation[j] = true;
                    }
                }
                oldRelationValues[i].free();
            }
        }
        BDD[] rallRelationValues;
        if (cache_before_rename) rallRelationValues = new BDD[top.size()];
        else rallRelationValues = allRelationValues;
        // Replace BDDDomain's in the BDD relations to match variable
        // assignments.
        for (int i = 0; i < top.size(); ++i) {
            RuleTerm rt = (RuleTerm) top.get(i);
            BDDRelation r = (BDDRelation) rt.relation;
            if (TRACE) solver.out.println("Relation " + r + " " + allRelationValues[i].nodeCount() + " nodes, domains "
                + domainsOf(allRelationValues[i]));
            if (TRACE_FULL) solver.out.println("   current value: " + allRelationValues[i].toStringWithDomains());
            BDDPairing pairing = renames[i];
            if (cache_before_rename) {
                if (pairing != null) {
                    if (newRelationValues[i] != null) {
                        if (TRACE) {
                            solver.out.print("Diff for Relation " + r + " domains " + domainsOf(newRelationValues[i]) + " -> ");
                            ttime = System.currentTimeMillis();
                        }
                        newRelationValues[i].replaceWith(pairing);
                        if (TRACE) {
                            solver.out.print(domainsOf(newRelationValues[i]));
                            solver.out.println(" (" + (System.currentTimeMillis() - ttime) + " ms)");
                        }
                    }
                    if (needWholeRelation[i]) {
                        if (TRACE) {
                            solver.out.print("Whole Relation " + r + " domains " + domainsOf(allRelationValues[i]) + " -> ");
                            ttime = System.currentTimeMillis();
                        }
                        rallRelationValues[i] = allRelationValues[i].replace(pairing);
                        if (TRACE) {
                            solver.out.print(domainsOf(rallRelationValues[i]));
                            solver.out.println(" (" + (System.currentTimeMillis() - ttime) + " ms)");
                        }
                    }
                }
                if (rallRelationValues[i] == null) {
                    rallRelationValues[i] = allRelationValues[i].id();
                }
            } else {
                if (pairing != null) {
                    if (TRACE) {
                        solver.out.print("Relation " + r + " domains " + domainsOf(allRelationValues[i]) + " -> ");
                        ttime = System.currentTimeMillis();
                    }
                    allRelationValues[i].replaceWith(pairing);
                    if (TRACE) {
                        solver.out.print(domainsOf(allRelationValues[i]));
                        solver.out.println(" (" + (System.currentTimeMillis() - ttime) + " ms)");
                    }
                }
                if (!allRelationValues[i].equals(oldRelationValues[i])) {
                    if (TRACE) {
                        solver.out.print("Diff relation #" + i + ": (" + allRelationValues[i].nodeCount() + "x" + oldRelationValues[i].nodeCount()
                            + "=");
                        ttime = System.currentTimeMillis();
                    }
                    newRelationValues[i] = allRelationValues[i].apply(oldRelationValues[i], BDDFactory.diff);
                    if (TRACE) {
                        solver.out.print(newRelationValues[i].nodeCount() + ")");
                        solver.out.println(" (" + (System.currentTimeMillis() - ttime) + " ms)");
                    }
                    if (TRACE_FULL) solver.out.println("New for relation " + r + ": " + newRelationValues[i].toStringWithDomains());
                }
                oldRelationValues[i].free();
            }
        }
        BDDRelation r = (BDDRelation) bottom.relation;
        if (TRACE_FULL) solver.out.println("Current value of relation " + bottom + ": " + r.relation.toStringWithDomains());  
        BDD[] newRelationValuesCopy = new BDD[newRelationValues.length];
        
        BDD[] results = evalRelationsIncremental(solver.bdd, newRelationValues, rallRelationValues, canQuantifyAfter);
        long thisTime = System.currentTimeMillis() - time;
        if (cache_before_rename) {
            for (int i = 0; i < rallRelationValues.length; ++i) {
                rallRelationValues[i].free();
            }
        }
        if (TRACE) solver.out.print("Result: ");
        BDD result = solver.bdd.zero();
        for (int i = 0; i < results.length; ++i) {
            if (results[i] != null) {
                if (TRACE) {
                    ttime = System.currentTimeMillis();
                }
                result.orWith(results[i]);
                if (TRACE) {
                    solver.out.print(" -> " + result.nodeCount());
                    solver.out.print(" (" + (System.currentTimeMillis() - ttime) + " ms)");
                }
            }
        }
        if (TRACE) solver.out.println(" -> " + result.nodeCount());
        if (single) {
            result = limitToSingle(result);
            if (TRACE) solver.out.println("Limited to single satisfying tuple: " + result.nodeCount());
        }
        if (bottomRename != null) {
            if (TRACE) {
                solver.out.print("Result domains: " + domainsOf(result) + " -> ");
                ttime = System.currentTimeMillis();
            }
            result.replaceWith(bottomRename);
            if (TRACE) {
                solver.out.print(domainsOf(result));
                solver.out.println(" (" + (System.currentTimeMillis() - ttime) + " ms)");
            }
        }
        for (int i = 0; i < bottom.variables.size(); ++i) {
            Variable v = (Variable) bottom.variables.get(i);
            if (v instanceof Constant) {
                Constant c = (Constant) v;
                BDDDomain d = (BDDDomain) r.domains.get(i);
                if (TRACE) {
                    solver.out.print("Restricting result domain " + d + " to constant " + c);
                    ttime = System.currentTimeMillis();
                }
                result.andWith(d.ithVar(c.value));
                if (TRACE) {
                    solver.out.println(" (" + (System.currentTimeMillis() - ttime) + " ms)");
                }
            }
        }
        BDD oldRelation = r.relation.id();
        if (TRACE_FULL) solver.out.println("Adding to " + bottom + ": " + result.toStringWithDomains());
        if (TRACE) {
            solver.out.print("Result: " + r.relation.nodeCount() + " nodes -> ");
            ttime = System.currentTimeMillis();
        }
        r.relation.orWith(result);
        if (TRACE) {
            solver.out.print(r.relation.nodeCount() + " nodes, " + r.dsize() + " elements.");
            solver.out.println(" (" + (System.currentTimeMillis() - ttime) + " ms)");
        }
        if (TRACE_FULL) solver.out.println("Relation " + r + " is now: " + r.relation.toStringWithDomains());
        boolean changed = !oldRelation.equals(r.relation);
        if (TRACE) solver.out.println("Relation " + r + " changed: " + changed);
        if (solver.REPORT_STATS) totalTime += System.currentTimeMillis() - time;
        if (TRACE) solver.out.println("Time spent: " + (System.currentTimeMillis() - time));
        r.updateNegated();
        r.doUpdate(oldRelation);
        if (r.negated != null) {
            BDD old_neg = oldRelation.not(); 
            ((BDDRelation)r.negated).doUpdate(old_neg);
            old_neg.free();
        }
        doPostUpdate(oldRelation);
        oldRelation.free();
        oldRelationValues = allRelationValues;
        return changed;
    }

    BDD limitToSingle(BDD result) {
        // Limit the result tuples to a single one.
        BDDVarSet set = solver.bdd.emptySet();
        for (Iterator k = bottom.variables.iterator(); k.hasNext(); ) {
            Variable v = (Variable) k.next();
            if (unnecessaryVariables.contains(v)) continue;
            BDDDomain d2 = (BDDDomain) variableToBDDDomain.get(v);
            set.unionWith(d2.set());
        }
        BDD singleResult = result.satOne(set, false);
        result.free();
        if (solver.NOISY) {
            solver.out.println("        Limiting result to a single tuple: "+singleResult.toStringWithDomains());
        }
        set.free();
        return singleResult;
    }
    
    public BDD[] evalRelationsIncremental(BDDFactory bdd, BDD[] newRelationValues, BDD[] rallRelationValues, BDDVarSet[] canQuantifyAfter){
        long ttime = 0;
        BDD[] results = new BDD[newRelationValues.length];
        outer : for (int i = 0; i < newRelationValues.length; ++i) {
            if (newRelationValues[i] == null) {
                if (TRACE) solver.out.println("Nothing new for " + (RuleTerm) top.get(i) + ", skipping.");
                continue;
            }
            Assert._assert(!newRelationValues[i].isZero());
            RuleTerm rt_new = (RuleTerm) top.get(i);
            results[i] = bdd.universe();
            for (int j = 0; j < rallRelationValues.length; ++j) {
                RuleTerm rt = (RuleTerm) top.get(j);
                BDDVarSet canNowQuantify = canQuantifyAfter[j];
                if (TRACE) solver.out.print(" x " + rt.relation);
                BDD b;
                if (i != j) {
                    b = rallRelationValues[j].id();
                } else {
                    b = newRelationValues[i];
                    if (TRACE) solver.out.print("'");
                }
                
                if (TRACE) {
                    solver.out.print(" (relprod " + b.nodeCount());
                }
                if (TRACE || find_best_order || DUMP_CUTOFF > 0) ttime = System.currentTimeMillis();
                BDD topBdd = results[i].relprod(b, canNowQuantify);
                if (TRACE || find_best_order || DUMP_CUTOFF > 0) ttime = System.currentTimeMillis() - ttime;
                if (TRACE) {
                    solver.out.print("=" + topBdd.nodeCount() + ")");
                    solver.out.print(" (" + ttime + " ms)");
                }
                if (DUMP_CUTOFF > 0 && ttime >= DUMP_CUTOFF && 
                    SystemProperties.getPropertyFromFile("dumpslow") != null) {
                    long ftime = System.currentTimeMillis();
                    // Dump this operation to disk so we can analyze it later.
                    try {
                        String baseName = solver.getBaseName()+"rule"+id+"_subgoal"+i+","+j+"_update"+updateCount;
                        Writer w = new FileWriter(baseName+".info");
                        w.write("Rule: "+this+"\n");
                        w.write("Time: "+ttime+" ms\n");
                        w.close();
                        BDDRelation.save(solver, baseName+"_op1.bdd", results[i]);
                        BDDRelation.save(solver, baseName+"_op2.bdd", b);
                        BDDRelation.save(solver, baseName+"_op3.bdd", canNowQuantify.toBDD());
                    } catch (IOException x) {
                        System.err.println("Error dumping BDD: "+x);
                    }
                    ftime = System.currentTimeMillis() - ftime;
                    this.totalTime -= ftime;
                }
                if (find_best_order && !results[i].isOne() && ttime >= FBO_CUTOFF) {
                    long ftime = System.currentTimeMillis();
                    FindBestDomainOrder.findBestDomainOrder(solver,this, top.size() + i*j,solver.bdd, results[i], b, canNowQuantify,
                        (RuleTerm) top.get(j-1), rt,
                        variableSet[j], rt.variables);
                    // Correct for learning time.
                    ftime = System.currentTimeMillis() - ftime;
                    this.totalTime -= ftime;
                }
                b.free();
                results[i].free();
                results[i] = topBdd;
                if (results[i].isZero()) {
                    if (TRACE) solver.out.println(" Became empty, skipping.");
                    if (j < i) newRelationValues[i].free();
                    continue outer;
                }
            }
            if (TRACE_FULL) solver.out.println(" = " + results[i].toStringWithDomains());
            else if (TRACE) solver.out.println(" = " + results[i].nodeCount()); 
        }
        return results;
    }
    /*
     * (non-Javadoc)
     * 
     * @see net.sf.bddbddb.InferenceRule#reportStats()
     */
    public void reportStats() {
        solver.out.println("Rule " + this);
        solver.out.println("   Updates: " + updateCount);
        solver.out.println("   Time: " + totalTime + " ms");
        solver.out.println("   Longest Iteration: " + longestIteration + " (" + longestTime + " ms)");
    }

    /**
     * Helper function to return a string of the domains of a given BDD.
     * 
     * @param b  input BDD
     * @return  string representation of the domains
     */
    private String domainsOf(BDD b) {
        BDDVarSet s = b.support();
        String result = domainsOf(s);
        s.free();
        return result;
    }

    private String domainsOf(BDDVarSet s) {
        BDDDomain[] a = s.getDomains();
        if (a.length == 0) return "(none)";
        StringBuffer sb = new StringBuffer();
        for (int i = 0; i < a.length; ++i) {
            sb.append(a[i]);
            if (i < a.length - 1) sb.append(',');
        }
        return sb.toString();
    }
    
    /*
     * (non-Javadoc)
     * 
     * @see net.sf.bddbddb.InferenceRule#free()
     */
    public void free() {
        super.free();
        if (oldRelationValues != null) {
            for (int i = 0; i < oldRelationValues.length; ++i) {
                if (oldRelationValues[i] != null) {
                    oldRelationValues[i].free();
                    oldRelationValues[i] = null;
                }
            }
        }
        if (canQuantifyAfter != null) {
            for (int i = 0; i < canQuantifyAfter.length; ++i) {
                if (canQuantifyAfter[i] != null) {
                    canQuantifyAfter[i].free();
                    canQuantifyAfter[i] = null;
                }
            }
        }
        if (renames != null) {
            for (int i = 0; i < renames.length; ++i) {
                if (renames[i] != null) {
                    // Don't reset, because it is shared across rules.
                    //renames[i].reset();
                    renames[i] = null;
                }
            }
        }
        if (bottomRename != null) {
            // Don't reset, because it is shared across rules.
            //bottomRename.reset();
            bottomRename = null;
        }
    }

    /**
     * Helper function to convert the given term to a string representation.
     * 
     * @param t  term
     * @return  string representation
     */
    private String termToString(RuleTerm t) {
        StringBuffer sb = new StringBuffer();
        sb.append(t.relation);
        sb.append("(");
        for (Iterator i = t.variables.iterator(); i.hasNext();) {
            Variable v = (Variable) i.next();
            sb.append(v);
            if (variableToBDDDomain != null) {
                BDDDomain d = (BDDDomain) variableToBDDDomain.get(v);
                if (d != null) {
                    sb.append(':');
                    sb.append(d.getName());
                }
            }
            if (i.hasNext()) sb.append(",");
        }
        sb.append(")");
        return sb.toString();
    }

    /*
     * (non-Javadoc)
     * 
     * @see java.lang.Object#toString()
     */
    public String toString() {
        StringBuffer sb = new StringBuffer();
        sb.append(termToString(bottom));
        sb.append(" :- ");
        for (Iterator i = top.iterator(); i.hasNext();) {
            RuleTerm t = (RuleTerm) i.next();
            sb.append(termToString(t));
            if (i.hasNext()) sb.append(", ");
        }
        sb.append(".");
        return sb.toString();
    }
    
    //// FindBestDomainOrder stuff below.
    
    public class VarOrderComparator implements Comparator {

        String varorder;
        
        public VarOrderComparator(String vo) {
            this.varorder = vo;
        }
        
        /* (non-Javadoc)
         * @see java.util.Comparator#compare(java.lang.Object, java.lang.Object)
         */
        public int compare(Object arg0, Object arg1) {
            if (arg0 == arg1) return 0;
            Variable v0 = (Variable) arg0;
            Variable v1 = (Variable) arg1;
            BDDDomain d0 = (BDDDomain) variableToBDDDomain.get(v0);
            BDDDomain d1 = (BDDDomain) variableToBDDDomain.get(v1);
            if (d0 == null) {
                if (d1 == null) return 0;
                return 1;
            } else if (d1 == null) {
                return -1;
            }
            int index0 = varorder.indexOf(d0.getName());
            int index1 = varorder.indexOf(d1.getName());
            if (index0 < index1) return -1;
            else if (index0 > index1) return 1;
            return 0;
        }
        
    }
    
    public static final long LONG_TIME = 10000000;
    public static int MAX_FBO_TRIALS = Integer.parseInt(SystemProperties.getProperty("fbotrials", "50"));
    
    int lastTrialNum = -1;
}