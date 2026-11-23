import { NextResponse } from "next/server";
import { readFileSync } from "fs";

const TOKEN =
  process.env.GH_TOKEN ||
  (() => {
    try {
      return readFileSync(
        "/home/z/bag/downloaded/extracted/erdos-zipbag/secrets/ghtoken.txt",
        "utf-8"
      ).trim();
    } catch {
      return "";
    }
  })();

const LANES = [
  "gst-finite-line-point-algebra",
  "gst-finite-line-honest-hodge-data",
  "gst-finite-line-cycle-correspondence",
  "gst-finite-line-world-discharge",
  "gst-finite-line-analytification",
  "gst-finite-line-riemann",
  "gst-finite-line-unconditional-source",
  "gst-finite-line-world",
  "gst-hypothesis-spanning-proof",
];

export const dynamic = "force-dynamic";

export async function GET() {
  if (!TOKEN) {
    return NextResponse.json(
      { lanes: [], error: "token unavailable" },
      { status: 200 }
    );
  }
  try {
    const res = await fetch(
      `https://api.github.com/repos/kyo-oo/HC-PROOF/actions/runs?per_page=40`,
      {
        headers: {
          Authorization: `token ${TOKEN}`,
          Accept: "application/vnd.github+json",
        },
        cache: "no-store",
      }
    );
    if (!res.ok) {
      return NextResponse.json({ lanes: [], error: `gh ${res.status}` });
    }
    const data = await res.json();
    const runs: Array<Record<string, unknown>> = (data.workflow_runs || [])
      .filter((r: Record<string, unknown>) =>
        LANES.includes(
          (r.name as string).toLowerCase().replace(/\s+/g, "-")
        )
      )
      .slice(0, 24)
      .map((r: Record<string, unknown>) => ({
        id: r.id,
        lane: r.name,
        sha: (r.head_sha as string)?.slice(0, 7),
        status: r.status,
        conclusion: r.conclusion,
        created: r.created_at,
        url: r.html_url,
      }));
    return NextResponse.json({ lanes: runs, fetched: Date.now() });
  } catch (e) {
    return NextResponse.json({ lanes: [], error: String(e) });
  }
}
