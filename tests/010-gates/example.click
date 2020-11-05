model lightclick

modules

alpha = module { s : logic general output high };
omega = module { s : logic general input  high };

a = module { s : logic general output high };
b = module { s : logic general output high };
c = module { s : logic general output high };
d = module { s : logic general output high };

e = module { s : logic general input high};

a_ = module { s : logic general output high };
b_ = module { s : logic general output high };
c_ = module { s : logic general output high };
d_ = module { s : logic general output high };

e_ = module { s : logic general input high};

a__ = module { s : logic general output high };
b__ = module { s : logic general output high };
c__ = module { s : logic general output high };
d__ = module { s : logic general output high };

e__ = module { s : logic general input high};


connections

alpha[s] ! omega[s];

{ a[s], b[s], c[s], d[s] } & e[s];

{ a_[s], b_[s], c_[s], d_[s] } | e_[s];

{ a__[s], b__[s], c__[s], d__[s] } + e__[s];

// -- [ EOF ]
