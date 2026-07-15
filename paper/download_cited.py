import re
import urllib.request
import os

# List of URLs from the user's prompt
urls = [
    "https://www.math.wustl.edu/~kumar/courses/310-2017/310W-2017/assignment2/chenthuran2_rieman_Paper.pdf",
    "https://noncommutativeanalysis.wordpress.com/wp-content/uploads/2025/10/on-riemanns-famous-paper-on-the-zeta-function-on-the-number-of-primes-less-than-a-given-magnitude.pdf",
    "https://www.mathlumen.com/articles/riemann-hypothesis-2026-status-report",
    "https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf",
    "https://arxiv.org/html/2308.11637v3",
    "https://www.claymath.org/library/annual_report/ar2004/04report_sarnak.pdf",
    "https://en.wikipedia.org/wiki/Riemann_hypothesis",
    "https://www.mdpi.com/2075-1680/14/3/169",
    "https://arxiv.org/pdf/2602.04022",
    "https://arxiv.org/abs/2602.04022",
    "https://www.researchgate.net/publication/398421128_NEW_HORIZONS_IN_RIEMANN_ZETA_FUNCTION_ANALYSIS_FROM_GUTH-MAYNARD_ESTIMATES_TO_THE_GADU-IOMM_OPERATORIAL_PARADIGM",
    "https://arxiv.org/html/2406.01828v2",
    "https://mathshistory.st-andrews.ac.uk/Extras/Borwein_Peter_books/",
    "https://aimath.org/~kaur/publications/90.pdf",
    "https://empslocal.ex.ac.uk/people/staff/mrwatkin/zeta/petersen.pdf",
    "https://scholar.utc.edu/cgi/viewcontent.cgi?article=1072&context=honors-theses",
    "https://www.claymath.org/collections/riemanns-1859-manuscript/",
    "https://arxiv.org/html/2607.04632v1",
    "https://web.williams.edu/Mathematics/sjmiller/public_html/372Fa17/addcomments/SondowHavilRHmm6.pdf",
    "https://journals.vilniustech.lt/index.php/MMA/article/download/23766/13020/107231",
    "https://www.mdpi.com/2073-8994/17/2/225",
    "https://gtbac.telecom-paristech.fr/slides/110114sole.pdf",
    "http://www.numbertheory.org/ntw/N12.html",
    "https://access.archive-ouverte.unige.ch/access/metadata/fb5fec20-db12-4e4a-8094-fdd63f4be46f/download",
    "https://libsearch.mtu.ie/cgi-bin/koha/opac-detail.pl?biblionumber=72009",
    "https://arxiv.org/pdf/0910.1534",
    "https://www.diva-portal.org/smash/get/diva2:752775/FULLTEXT01.pdf",
    "https://www.diva-portal.org/smash/get/diva2:1741450/FULLTEXT01.pdf",
    "https://insa.nic.in/writereaddata/UpLoadedFiles/IJPAM/Vol54_2023_1_ART13.pdf",
    "https://www.preprints.org/frontend/manuscript/c49b2104e2dec334f7410946bd7d442d/download_pub",
    "https://arxiv.org/html/2404.00583v2",
    "https://sas.rochester.edu/mth/people/faculty/gonek-steve/assets/pdf/simplezeros.pdf",
    "http://www.paris8.free.fr/Titchmarsh_TheTheoryoftheRiemannZeta-Function.pdf",
    "https://resources.saylor.org/wwwresources/archived/site/wp-content/uploads/2012/06/MA111_Wikipedia_Riemann-Hypothesis_6.8.2012.pdf",
    "https://www.semanticscholar.org/paper/THE-ZETA-FUNCTION-AND-THE-RIEMANN-HYPOTHESIS-Moros/de22bcaea8f92bc4c9300e97e6fe107dbb0af154",
    "https://www.parabola.unsw.edu.au/sites/default/files/2025-12/vol61_no3_5.pdf",
    "https://brittlebooks.library.illinois.edu/brittlebooks_closed/Books2011-10/titced0001zetof/titced0001zetof.pdf",
    "http://www.stat.ucla.edu/~ywu/Riemann.pdf",
    "https://www.researchgate.net/publication/321604779_Equivalents_of_the_Riemann_Hypothesis_Volume_One_Arithmetic_Equivalents",
    "https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/references/D4D9776E95DCB5FF59049228407BE45E",
    "https://mwolf.pracownicy.uksw.edu.pl/rare.html",
    "https://arxiv.org/pdf/1602.01799",
    "https://ssmr.ro/bulletin/pdf/63-1/articol_4.pdf",
    "https://empslocal.ex.ac.uk/people/staff/mrwatkin/zeta/xray2.pdf",
    "https://www.cmup.pt/sites/default/files/2023-11/RHALF_CMUP_4.pdf",
    "https://scispace.com/pdf/review-e-c-titchmarsh-the-theory-of-the-riemann-zeta-55gp2iudjk.pdf",
    "https://digitalcommons.isical.ac.in/masters-dissertations/41/",
    "https://es.wikipedia.org/wiki/Hip%C3%B3tesis_de_Riemann",
    "https://arxiv.org/pdf/math/0401126",
    "https://empslocal.ex.ac.uk/people/staff/mrwatkin/zeta/bump-zeros.pdf",
    "https://teorth.github.io/expdb/blueprint/zero-density-chapter.html",
    "https://www.cambridge.org/core/services/aop-cambridge-core/content/view/B4EC068F70EBCBA86E5F536F75444DCE/S1446788700034984a.pdf/hardys-legacy-to-number-theory.pdf",
    "https://arxiv.org/abs/2607.04632",
    "https://www.themoonlight.io/de/review/a-decades-long-breakthrough-in-zero-density-estimates-and-primes-in-short-intervals",
    "https://mathoverflow.net/questions/52576/zeta-function-zero-density-theorems",
    "https://matwbn.icm.edu.pl/ksiazki/aa/aa32/aa3216.pdf",
    "https://projecteuclid.org/journals/annals-of-mathematics/volume-203/issue-2/New-large-value-estimates-for-Dirichlet-polynomials/10.4007/annals.2026.203.2.6.full",
    "https://archive.org/details/riemannszetafunc00edwa_0",
    "https://scispace.com/papers/petites-valeurs-de-la-fonction-d-euler-1uw3j2wt4a",
    "https://books.google.com/books/about/Riemann_s_Zeta_Function.html?id=ruVmGFPwNhQC",
    "http://numbers.computation.free.fr/Constants/Miscellaneous/zetaevaluations.pdf",
    "https://sites.math.rutgers.edu/~zeilberg/EM18/TitchmarshZeta.pdf",
    "https://www.themoonlight.io/en/review/the-riemann-hypothesis-past-present-and-a-letter-through-time",
    "https://www.researchgate.net/profile/Jorgen-Veisdal/publication/354172739_Prime_Numbers_and_the_Riemann_Zeta_Function/links/61293c492b40ec7d8bca2d56/Prime-Numbers-and-the-Riemann-Zeta-Function.pdf",
    "https://www.numdam.org/articles/10.5802/cml.71/"
]

os.makedirs('pdf_links', exist_ok=True)
count = 0
for i, url in enumerate(urls):
    if url.endswith('.pdf') or 'pdf' in url.lower():
        try:
            filename = f"pdf_links/paper_{i}.pdf"
            print(f"Downloading {url} ...")
            req = urllib.request.Request(url, headers={'User-Agent': 'Mozilla/5.0'})
            with urllib.request.urlopen(req, timeout=10) as response, open(filename, 'wb') as out_file:
                out_file.write(response.read())
            count += 1
        except Exception as e:
            print(f"Failed {url}: {e}")

print(f"Downloaded {count} PDFs.")
