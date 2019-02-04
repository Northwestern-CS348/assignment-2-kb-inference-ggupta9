import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        if isinstance(fact_or_rule, Fact): #Checking to see if it is a fact
            if not fact_or_rule in self.facts: #Checking to see if it is in the DB
                return
            factRetract = self._get_fact(fact_or_rule) #Create fact to retract/remove
            if not factRetract.supported_by: #If fact not supported_by

                for p in factRetract.supported_by:
                    for q in p:
                        q.supports_facts.remove(factRetract) #Remove factRetract from all supporting facts

                for r in factRetract.supports_facts:
                    r.supported_by = [p for p in r.supported_by if p[0]!=factRetract]
                    self.kb_retract(r) #Remove the retracted fact from the fact it supports

                for s in factRetract.supports_rules:
                    s.supported_by = [p for p in s.supported_by if p[0]!=factRetract]
                    self.kb_retract(s) #Remove the rules the fact supports
                self.facts.remove(factRetract) #Remove the fact

        elif isinstance(fact_or_rule, Rule): #Checking to see if it is a rule
            if not fact_or_rule in self.facts: #Checking to see if it is in the DB
                return
            ruleRetract = self._get_rule(fact_or_rule) #Create rule to retract/remove
            if not ruleRetract.asserted: #If rule not asserted

                for p in ruleRetract.supported_by:
                    for q in p:
                        q.supports_rules.remove(ruleRetract) #Remove ruleRetract from all supporting rules

                for r in ruleRetract.supports_facts:
                    r.supported_by = [p for p in r.supported_by if p[1]!=ruleRetract]
                    self.kb_retract(r) #Remove the retracted rule from the fact it supports

                for s in ruleRetract.supports_rules:
                    s.supported_by = [p for p in s.supported_by if pair[1]!=ruleRetract]
                    self.kb_retract(s) #Remove the rules the fact supports
                self.rules.remove(ruleRetract) #Remove the rule


class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here
        bindingsList = match(fact.statement, rule.lhs[0])
        if bindingsList:

            if len(rule.lhs)==1: # add new rule if lhs = 1
                newState = instantiate(rule.rhs, bindingsList)
                newFact = Fact(newState, supported_by=[[fact, rule]]) #Create new fact to infer
                kb.kb_add(newFact) #Add fact to KB
                newFact = kb._get_fact(newFact) #Update subsequent supported/supporting facts
                fact.supports_facts.append(newFact)
                rule.supports_facts.append(newFact)

            elif len(rule.lhs)>1: # update inference engine with new lhs and rhs
                newRight = instantiate(rule.rhs, bindingsList) #Create new rhs
                newLeft = [instantiate(i, bindingsList) for i in rule.lhs[1:]] #Create new lhs
                newRule = Rule([newLeft, newRight], supported_by=[[fact, rule]])
                kb.kb_add(newRule) #Add new rule
                newRule = kb._get_rule(newRule)
                fact.supports_rules.append(newRule)
                rule.supports_rules.append(newRule)
                
        else:
            return
