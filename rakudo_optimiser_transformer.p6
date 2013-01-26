sub try_nqp_transform($code, $transform) {
    pir::load_language__0s('nqp');
    my $nqp := pir::compreg__Ps('nqp');
    my $p6 := pir::compreg__Ps('perl6');

    my $qast := $p6.compile($code, :target('past'));
    my $comp := $nqp.compile($transform);
    my $res  := nqp::atpos($comp, 1)($qast);
    my $pbc  := $p6.evalpmc($p6.pir($p6.post($res)));
    $pbc();
}

try_nqp_transform(q:to/P6CODE/, q:to/NQPCODE/);
    sub test() { say "side effect!"; 3 }
    if test()|test()|test() == test() { say "ah" };
    #if 1 == 3 || 2 == 3 || 3 == 3 { say "ah" };
    P6CODE
    sub transform($node) {
        print($node.dump);
        my $depth := 0;
        my @bstack := [$node[0]];
        sub msay($txt) {
            my $d := 0;
            while $d <= $depth {
                print("|  ");
                $d := $d + 1;
            }

            say($txt);
        }
        sub find_lexical($name) {
            my $i := +@bstack;
            while $i > 0 {
                $i := $i - 1;
                my $block := @bstack[$i];
                my %sym := $block.symbol($name);
                if +%sym {
                    if nqp::existskey(%sym, 'value') {
                        return %sym<value>;
                    }
                    else {
                        nqp::die("Optimizer: No lexical compile time value for $name");
                    }
                }
            }
            nqp::die("Optimizer: No lexical $name found");
        }
        sub find_core() {
            my $i := +@bstack;
            while $i > 0 {
                $i := $i - 1;
                my $block := @bstack[$i];
                my %sym := $block.symbol("!CORE_MARKER");
                if +%sym {
                    return $block;
                }
            }
            nqp::die("Optimizer: couldn't locate !CORE_MARKER");
        }
        sub lexical_in($block, $name) {
            my %sym := $block.symbol($name);
            if +%sym {
                if nqp::existskey(%sym, 'value') {
                    return %sym<value>;
                }
                else {
                    nqp::die("Optimizer: No lexical compile time value for $name");
                }
            }
            return 0;
        }
        sub can_chain_junction_be_warped($node) {
            sub has_core-ish_junction($node) {
                if nqp::istype($node, QAST::Op) && $node.op eq 'call' && $node.name {
                    # TODO: add &infix:<^> to the list
                    if $node.name eq '&infix:<|>' || $node.name eq '&infix:<&>' {
                        my $callee := find_lexical($node.name);
                        my $core := find_core();
                        if lexical_in($core, $node.name) eq $callee {
                            msay("found this " ~ $node.name ~ " in the core");
                            return 1;
                        }
                    }
                }
                return 0;
            }
            my @warpable := [has_core-ish_junction($node[0]), has_core-ish_junction($node[1])];
            return @warpable;
        }
        sub visit_op($node) {
            msay("visiting op " ~ $node.dump_extra_node_info());
            if $node.op eq "if" || $node.op eq "unless" {
                if nqp::istype($node[0], QAST::Op) && $node[0].op eq "chain" {
                    if my @warpable := can_chain_junction_be_warped($node[0]) {
                        if @warpable[0] {
                            msay("unfolding the left side");
                            my $juncop := $node[0][0].name eq '&infix:<|>' ?? 'if' !! 'unless';
                            my $juncname := $node[0][0].name eq '&infix:<&>' ?? '&infix:<&&>' !! '&infix:<||>';
                            my $chainop := $node[0].op;
                            my $chainname := $node[0].name;
                            my $values := $node[0][0];
                            my $rvalue := $node[0][1];
                            my %reference;
                            sub refer_to($valnode) {
                                my $id := $valnode;
                                if nqp::existskey(%reference, $id) {
                                    return QAST::Var.new(:name(%reference{$id}), :scope<local>);
                                }
                                %reference{$id} := $node.unique('junction_unfold');
                                return QAST::Op.new(:op<bind>,
                                                    QAST::Var.new(:name(%reference{$id}),
                                                                  :scope<local>,
                                                                  :decl<var>),
                                                    $valnode);
                            }
                            sub chain($value) {
                                return QAST::Op.new(:op($chainop), :name($chainname),
                                                    refer_to($value),
                                                    refer_to($rvalue));
                            }
                            sub create_junc() {
                                my $junc := QAST::Op.new(:op($juncop), :name($juncname));
                                while +$values.list {
                                    $junc.push(chain($values.shift()));
                                }
                                return $junc;
                            }
                            $node.shift;
                            $node.unshift(create_junc());
                            return visit($node);
                        } elsif @warpable[1] {
                            msay("not going to unfold the right side yet.");
                        }
                    }
                }
            }
            return visit($node);
        }
        sub visit($node, :$skip_selectors) {
            my $i := 0;
            $depth := $depth + 1;
            while $i < +@($node) {
                unless $skip_selectors && $i % 2 {
                    my $visit := $node[$i];
                    if nqp::istype($visit, QAST::Op) {
                        #$node[$i] := self.visit_op($visit)
                        $node[$i] := visit_op($visit);
                    }
                    elsif nqp::istype($visit, QAST::Want) {
                        #self.visit_want($visit);
                        msay('Want found');
                        if $visit.has_compile_time_value() {
                            msay("ctv: " ~ $visit.compile_time_value());
                        }
                        $node[$i] := visit($visit);
                    }
                    elsif nqp::istype($visit, QAST::Var) {
                        #self.visit_var($visit);
                        msay('Var found ' ~ $visit.dump_extra_node_info());
                        $node[$i] := visit($visit);
                    }
                    elsif nqp::istype($visit, QAST::Block) {
                        #$node[$i] := self.visit_block($visit);
                        msay('Block found');
                        $node[$i] := visit($visit);
                    }
                    elsif nqp::istype($visit, QAST::Stmts) {
                        #self.visit_children($visit);
                        msay('Stmts found');
                        $node[$i] := visit($visit);
                    }
                    elsif nqp::istype($visit, QAST::Stmt) {
                        #self.visit_children($visit);
                        msay('Stmt found');
                        $node[$i] := visit($visit);
                    }
                }
                $i := $i + 1;
            }
            $depth := $depth - 1;
            $node;
        }

        say("in transformer");
        visit($node);
        say("visited.");
        say($node.dump);
        $node
    }
    NQPCODE
